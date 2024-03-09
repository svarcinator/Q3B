#include "ExprToBDDTransformer.h"

#include "ExpensiveOp.h"
#include "HexHelper.h"
#include "Solver.h"
#include "BvecTester.h"

#include <algorithm>
#include <cmath>
#include <list>
#include <sstream>

#define DEBUG false

const unsigned int precisionMultiplier = 1000;

using namespace std;
using namespace z3;
using namespace std::placeholders;

ExprToBDDTransformer::ExprToBDDTransformer(z3::context &ctx, z3::expr e, Config config)
    : config(config), expression(e)
{
    this->context = &ctx;
    configureReorder();

    loadVars();
    //setApproximationType(ZERO_EXTEND);
    setApproximationType(SIGN_EXTEND); // why? -- under and over appr set appr type themselves, no appr does not need it
}

void ExprToBDDTransformer::getVars(const z3::expr &e)
{
    if (processedVarsCache.find((Z3_ast) e) != processedVarsCache.end()) {
        return;
    }

    if (e.is_const() && !e.is_numeral()) {
        std::unique_lock<std::mutex> lk(Solver::m_z3context);
        std::string expressionString = e.to_string();

        if (expressionString == "true" || expressionString == "false") {
            return;
        }

        int bitWidth = e.get_sort().is_bool() ? 1 : e.get_sort().bv_size();
        constSet.insert(make_pair(expressionString, bitWidth));
        varSorts.emplace(expressionString, e.get_sort());
    } else if (e.is_app()) {
        func_decl f = e.decl();
        unsigned num = e.num_args();

        for (unsigned i = 0; i < num; i++) {
            getVars(e.arg(i));
        }
    } else if (e.is_quantifier()) {
        Z3_ast ast = (Z3_ast) e;

        int boundVariables = Z3_get_quantifier_num_bound(*context, ast);

        for (int i = 0; i < boundVariables; i++) {
            Z3_symbol z3_symbol = Z3_get_quantifier_bound_name(*context, ast, i);
            Z3_sort z3_sort = Z3_get_quantifier_bound_sort(*context, ast, i);

            symbol current_symbol(*context, z3_symbol);
            z3::sort current_sort(*context, z3_sort);

            std::unique_lock<std::mutex> lk(Solver::m_z3context);
            var c = make_pair(current_symbol.str(), current_sort.is_bool() ? 1 : current_sort.bv_size());
            boundVarSet.insert(c);
            varSorts.emplace(current_symbol.str(), e.get_sort());
        }

        getVars(e.body());
    }

    processedVarsCache.insert((Z3_ast) e);
}

void ExprToBDDTransformer::loadVars()
{
    getVars(expression);
    processedVarsCache.clear();

    set<var> allVars;
    allVars.insert(constSet.begin(), constSet.end());
    allVars.insert(boundVarSet.begin(), boundVarSet.end());

    if (allVars.size() == 0) {
        return;
    }

    VariableOrderer orderer(allVars, *context);
    orderer.OrderFor(expression);

    vector<list<var>> orderedGroups = orderer.GetOrdered();

    int maxBitSize = 0;
    for (auto const &v : allVars) {
        if (v.second > maxBitSize)
            maxBitSize = v.second;
    }

    int offset = 0;
    for (auto const &group : orderedGroups) {
        int i = 0;
        for (auto const &v : group) {
            int bitnum = v.second;
            Bvec varBvec = Bvec::bvec_var(bddManager, bitnum, offset + i, group.size());
            vars.insert({ v.first, varBvec });

            int currentVar = offset + i;

            varIndices[v.first] = vector<int>();

            BDD varSet = bddManager.bddOne();
            for (int bit = 0; bit < bitnum; bit++) {
                varIndices[v.first].push_back(currentVar);
                varSet = varSet * varBvec[bit].GetBDD(bddManager.bddZero());
                currentVar += group.size();
            }

            varSets.insert({ v.first, varSet });

            i++;
        }

        offset += maxBitSize * group.size();
    }
}

BDDInterval ExprToBDDTransformer::loadBDDsFromExpr(expr e)
{
    caches.clearCurrentBwAndPrecCaches();

    cacheHits = 0;
    if(lastBW < 2){
        caches.sameBWPreciseBvecs.clear();  // deal with -1 later (does it change something?)
    }
    if (lastBW != variableBitWidth) {   // bitWidth changed
        incrementedApproxStyle = BIT_WIDTH;
        caches.variableBitWidth = variableBitWidth;
        caches.setCurrentBWasPrevBW();  // coppies precise bvec, so the can be used in further computation
        caches.clearCurrentBwCaches();
        lastBW = variableBitWidth;
    } else {
        incrementedApproxStyle = PRECISION;
    }
    //std::cout << caches.to_string();
    this->expression = e;
    //variableApproximationHappened = true;  //doesnt seem to be used anywhere
    auto result = getBDDFromExpr(e, {}, true, true);

    operationApproximationHappened = !result.IsPrecise();

    caches.clearCurrentBwAndPrecCaches();

    return result;
}

BDDInterval ExprToBDDTransformer::getConjunctionBdd(const vector<expr> &arguments, const vector<boundVar> &boundVars, bool onlyExistentials, bool isPositive)
{
    return getConnectiveBdd(
            arguments, boundVars, onlyExistentials, isPositive, [](auto &a, auto &b) { return a * b; }, [](const auto a) { return a.upper.IsZero(); }, BDDInterval{ bddManager.bddOne() });
}

BDDInterval ExprToBDDTransformer::getDisjunctionBdd(const vector<expr> &arguments, const vector<boundVar> &boundVars, bool onlyExistentials, bool isPositive)
{
    return getConnectiveBdd(
            arguments, boundVars, onlyExistentials, isPositive, [](auto &a, auto &b) { return a + b; }, [](const auto a) { return a.lower.IsOne(); }, BDDInterval{ bddManager.bddZero() });
}

uint ExprToBDDTransformer::posToEvaluate(const z3::expr &e1, const z3::expr &e2)
{
    ExpensiveOp opCounter;
    auto n1 = opCounter.getExpensiveOpNum(e1);
    auto n2 = opCounter.getExpensiveOpNum(e2);
    return (n1 <= n2) ? 1 : 0;
}

BDDInterval ExprToBDDTransformer::getImplSubBDD(const uint pos, const z3::expr &e, const vector<boundVar> &boundVars, bool onlyExistentials, bool isPositive)
{
    return (pos == 0) ? !getBDDFromExpr(e.arg(0), boundVars, onlyExistentials, !isPositive)
                      : getBDDFromExpr(e.arg(1), boundVars, onlyExistentials, isPositive);
}

BDDInterval ExprToBDDTransformer::getBDDFromExpr(const expr &e, const vector<boundVar> &boundVars, bool onlyExistentials, bool isPositive)
{
    assert(e.is_bool());

    auto cachedExpr = caches.foundExprInCaches(e, boundVars, isPositive);
    if (cachedExpr.has_value()) {
        return cachedExpr.value();
    }

    if (e.is_var()) {
        Z3_ast ast = (Z3_ast) e;
        int deBruijnIndex = Z3_get_index_value(*context, ast);
        boundVar bVar = boundVars[boundVars.size() - deBruijnIndex - 1];
        return BDDInterval{ (vars.at(bVar.first) == Bvec::bvec_true(bddManager, 1)).GetBDD(bddManager.bddZero()) };
    } else if (e.is_const()) {
        if (e.is_app() && e.decl().decl_kind() == Z3_OP_TRUE) {
            return BDDInterval{ bddManager.bddOne() };
        } else if (e.is_app() && e.decl().decl_kind() == Z3_OP_FALSE) {
            return BDDInterval{ bddManager.bddZero() };
        }

        Solver::m_z3context.lock();
        std::string exprString = e.to_string();
        Solver::m_z3context.unlock();

        return caches.insertIntoCaches(e, BDDInterval{ (vars.at(exprString) == Bvec::bvec_true(bddManager, 1)).GetBDD(bddManager.bddZero()) }, boundVars, isPositive);
    } else if (e.is_app()) {
        func_decl f = e.decl();
        unsigned num = e.num_args();

        auto decl_kind = f.decl_kind();

        if (decl_kind == Z3_OP_EQ) {
            checkNumberOfArguments<2>(e);

            auto sort = e.arg(0).get_sort();
            BDDInterval result;

            assert(sort.is_bv() || sort.is_bool());
            if (sort.is_bv()) {
                MaybeBDD::ResetApproximationFlag();
                if (config.approximationMethod == OPERATIONS || config.approximationMethod == BOTH) {
                    auto arg0 = getBvecFromExpr(e.arg(0), boundVars).value;
                    auto arg1 = getBvecFromExpr(e.arg(1), boundVars).value;

                    if (isPositive) {
                        return BDDInterval{ Bvec::bvec_equ_overApprox(arg0, arg1),
                            Bvec::bvec_equ_underApprox(arg0, arg1) };
                    } else {
                        return BDDInterval{ Bvec::bvec_equ_underApprox(arg0, arg1),
                            Bvec::bvec_equ_overApprox(arg0, arg1) };
                    }
                } else {
                    result = BDDInterval(Bvec::bvec_equ(getBvecFromExpr(e.arg(0), boundVars).value,
                            getBvecFromExpr(e.arg(1), boundVars).value)
                                                 .GetBDD(bddManager.bddZero()));
                }
            } else if (sort.is_bool()) {
                result = getBDDFromExpr(e.arg(0), boundVars, false, isPositive).Xnor(getBDDFromExpr(e.arg(1), boundVars, false, isPositive));
            }

            return caches.insertIntoCaches(e, result, boundVars, isPositive);
        } else if (decl_kind == Z3_OP_NOT) {
            return !getBDDFromExpr(e.arg(0), boundVars, onlyExistentials, !isPositive);
        } else if (decl_kind == Z3_OP_AND) {
            vector<expr> arguments;

            for (unsigned int i = 0; i < num; i++) {
                arguments.push_back(e.arg(i));
            }

            auto result = getConjunctionBdd(arguments, boundVars, onlyExistentials, isPositive);
            return caches.insertIntoCaches(e, result, boundVars, isPositive);
        } else if (decl_kind == Z3_OP_OR) {
            vector<expr> arguments;
            for (unsigned int i = 0; i < num; i++) {
                arguments.push_back(e.arg(i));
            }

            auto result = getDisjunctionBdd(arguments, boundVars, onlyExistentials, isPositive);
            return caches.insertIntoCaches(e, result, boundVars, isPositive);
        } else if (decl_kind == Z3_OP_IMPLIES) {
            checkNumberOfArguments<2>(e);
            BDDInterval result;

            if (config.lazyEvaluation) {
                auto posToEval = posToEvaluate(e.arg(0), e.arg(1));
                result = getImplSubBDD(posToEval, e.arg(posToEval), boundVars, onlyExistentials, isPositive);
                if (!result.lower.IsOne()) {
                    result = result + getImplSubBDD(1 - posToEval, e.arg(1 - posToEval), boundVars, onlyExistentials, isPositive);
                }
            } else {
                result = !getBDDFromExpr(e.arg(0), boundVars, onlyExistentials, !isPositive) +
                        getBDDFromExpr(e.arg(1), boundVars, onlyExistentials, isPositive);
            }
            return caches.insertIntoCaches(e, result, boundVars, isPositive);
        } else if (decl_kind == Z3_OP_ULEQ) {
            checkNumberOfArguments<2>(e);

            auto arg0 = getBvecFromExpr(e.arg(0), boundVars).value;
            auto arg1 = getBvecFromExpr(e.arg(1), boundVars).value;

            return caches.insertIntoCaches(e, bvec_ule(arg0, arg1, isPositive), boundVars, isPositive);
        } else if (decl_kind == Z3_OP_ULT) {
            checkNumberOfArguments<2>(e);

            auto arg0 = getBvecFromExpr(e.arg(0), boundVars).value;
            auto arg1 = getBvecFromExpr(e.arg(1), boundVars).value;

            return caches.insertIntoCaches(e, bvec_ult(arg0, arg1, isPositive), boundVars, isPositive);
        } else if (decl_kind == Z3_OP_UGEQ) {
            checkNumberOfArguments<2>(e);

            auto arg0 = getBvecFromExpr(e.arg(0), boundVars).value;
            auto arg1 = getBvecFromExpr(e.arg(1), boundVars).value;

            return caches.insertIntoCaches(e, bvec_ule(arg1, arg0, isPositive), boundVars, isPositive);
        } else if (decl_kind == Z3_OP_UGT) {
            checkNumberOfArguments<2>(e);

            auto arg0 = getBvecFromExpr(e.arg(0), boundVars).value;
            auto arg1 = getBvecFromExpr(e.arg(1), boundVars).value;

            return caches.insertIntoCaches(e, bvec_ult(arg1, arg0, isPositive), boundVars, isPositive);
        } else if (decl_kind == Z3_OP_SLEQ) {
            checkNumberOfArguments<2>(e);
            
            BDD result;
            
            auto arg0 = getBvecFromExpr(e.arg(0), boundVars).value;
            auto arg1 = getBvecFromExpr(e.arg(1), boundVars).value;

            if ( (config.approximationMethod == OPERATIONS || config.approximationMethod == BOTH)) {
                auto over = Bvec::bvec_slte_overApprox(arg0, arg1);

                Bvec leastNumber = Bvec::bvec_false(bddManager, arg0.bitnum());
                leastNumber.set(arg0.bitnum() - 1, MaybeBDD(bddManager.bddOne()));

                Bvec greatestNumber = Bvec::bvec_true(bddManager, arg0.bitnum());
                greatestNumber.set(arg0.bitnum() - 1, MaybeBDD(bddManager.bddZero()));
                auto under = Bvec::bvec_slte_underApprox(arg0, arg1) |
                        Bvec::bvec_equ_underApprox(arg0, leastNumber) |
                        Bvec::bvec_equ_underApprox(arg1, greatestNumber);

                return isPositive ? BDDInterval(over, under) : BDDInterval(under, over);
            } else {
                result = Bvec::bvec_slte(arg0, arg1).GetBDD(bddManager.bddZero());
            }

            return caches.insertIntoCaches(e, BDDInterval{ result }, boundVars, isPositive);
        } else if (decl_kind == Z3_OP_SLT) {
            checkNumberOfArguments<2>(e);
            
            BDD result;
            auto arg0 = getBvecFromExpr(e.arg(0), boundVars).value;
            auto arg1 = getBvecFromExpr(e.arg(1), boundVars).value;

            if ( (config.approximationMethod == OPERATIONS || config.approximationMethod == BOTH)) {
                Bvec leastNumber = Bvec::bvec_false(bddManager, arg0.bitnum());
                leastNumber.set(arg0.bitnum() - 1, MaybeBDD(bddManager.bddOne()));

                Bvec greatestNumber = Bvec::bvec_true(bddManager, arg0.bitnum());
                greatestNumber.set(arg0.bitnum() - 1, MaybeBDD(bddManager.bddZero()));

                auto over = Bvec::bvec_slth_overApprox(arg0, arg1) &
                        Bvec::bvec_nequ_overApprox(arg0, greatestNumber) &
                        Bvec::bvec_nequ_overApprox(arg1, leastNumber);
                auto under = Bvec::bvec_slth_underApprox(arg0, arg1);

                return isPositive ? BDDInterval(over, under) : BDDInterval(under, over);
            } else {
                result = Bvec::bvec_slth(arg0, arg1).GetBDD(bddManager.bddZero());
            }

            return caches.insertIntoCaches(e, BDDInterval{ result }, boundVars, isPositive);
        } else if (decl_kind == Z3_OP_IFF) {
            checkNumberOfArguments<2>(e);

            auto arg0 = getBDDFromExpr(e.arg(0), boundVars, false, isPositive);
            auto arg1 = getBDDFromExpr(e.arg(1), boundVars, false, isPositive);

            auto result = arg0.Xnor(arg1);
            return caches.insertIntoCaches(e, result, boundVars, isPositive);
        } else if (decl_kind == Z3_OP_ITE) {
            checkNumberOfArguments<3>(e);

            auto arg0 = getBDDFromExpr(e.arg(0), boundVars, onlyExistentials, isPositive);
            BDDInterval result;
            if (config.lazyEvaluation && arg0.lower.IsOne()) {
                result = getBDDFromExpr(e.arg(1), boundVars, onlyExistentials, isPositive);
            }

            else if (config.lazyEvaluation && arg0.upper.IsZero()) {
                result = getBDDFromExpr(e.arg(2), boundVars, onlyExistentials, isPositive);
            } else {
                auto arg1 = getBDDFromExpr(e.arg(1), boundVars, onlyExistentials, isPositive);
                auto arg2 = getBDDFromExpr(e.arg(2), boundVars, onlyExistentials, isPositive);
                result = arg0.Ite(arg1, arg2);
            }

            return caches.insertIntoCaches(e, result, boundVars, isPositive);
        } else {
            cout << "function " << f.name().str() << endl;
            exit(1);
        }
    } else if (e.is_quantifier()) {
        auto newBoundVars = getNewBounds(e, boundVars);
        int boundVariables = Z3_get_quantifier_num_bound(*context, (Z3_ast) e);
        BDDInterval bodyBdd;
        if (onlyExistentials) {
            if (Z3_is_quantifier_forall(*context, (Z3_ast) e)) {
                //only existentials so far, but this one is universal
                //auto oldsameBWImpreciseBvecStates = caches.sameBWImpreciseBvecStates;
                //caches.sameBWImpreciseBvecStates.clear();
                bodyBdd = getBDDFromExpr(e.body(), newBoundVars, false, isPositive);
                // TODO findout what is wrong here
                //caches.sameBWImpreciseBvecStates = oldsameBWImpreciseBvecStates;
            } else {
                //only existentials so far and this one is also existential
                auto oldBDDCache = caches.bddExprCache;
                auto oldBvecCache = caches.bvecExprCache;
                auto result = getBDDFromExpr(e.body(), newBoundVars, true, isPositive);
                //we need to revert the state of the cache, because of
                //the bound variables with the same names
                caches.bddExprCache = oldBDDCache;
                caches.bvecExprCache = oldBvecCache;

                return result;
            }
        } else {
            bodyBdd = getBDDFromExpr(e.body(), newBoundVars, false, isPositive);
        }

        //prune caches that will never be used again
        caches.pruneBddCache(newBoundVars);
        caches.pruneBvecCache(newBoundVars);

        for (int i = boundVariables - 1; i >= 0; i--) {
            Z3_symbol z3_symbol = Z3_get_quantifier_bound_name(*context, (Z3_ast) e, i);
            symbol current_symbol(*context, z3_symbol);

            Solver::m_z3context.lock();
            auto varSet = varSets.at(current_symbol.str());
            Solver::m_z3context.unlock();
            if (Z3_is_quantifier_forall(*context, (Z3_ast) e)) {
                bodyBdd = bodyBdd.UnivAbstract(varSet);
            } else {
                bodyBdd = bodyBdd.ExistAbstract(varSet);
            }
        }

        return caches.insertIntoCaches(e, bodyBdd, boundVars, isPositive);
    }

    cout << "bdd else: " << e << endl;
    abort();
}
std::vector<boundVar> ExprToBDDTransformer::getNewBounds(const z3::expr &e, const std::vector<boundVar> &boundVars)
{
    Z3_ast ast = (Z3_ast) e;

    int boundVariables = Z3_get_quantifier_num_bound(*context, ast);

    auto newBoundVars = boundVars;
    for (int i = 0; i < boundVariables; i++) {
        Z3_symbol z3_symbol = Z3_get_quantifier_bound_name(*context, ast, i);
        symbol current_symbol(*context, z3_symbol);

        BoundType bt = Z3_is_quantifier_forall(*context, ast) ? UNIVERSAL : EXISTENTIAL;

        std::unique_lock<std::mutex> lk(Solver::m_z3context);
        newBoundVars.push_back(std::pair<std::string, BoundType>(current_symbol.str(), bt));
    }
    return newBoundVars;
}

Approximated<Bvec> ExprToBDDTransformer::getApproximatedVariable(const std::string &varName, int newBitWidth, const ApproximationType &at)
{
    Bvec var = vars.at(varName);
    if (newBitWidth == 0) {
        return { var, PRECISE, PRECISE };
    }

    //variableApproximationHappened = true;

    bool flip = newBitWidth < 0;
    newBitWidth = abs(newBitWidth);

    newBitWidth = min(newBitWidth, (int) var.bitnum());
    int leftBits = newBitWidth / 2;
    int rightBits = newBitWidth - leftBits;

    if (flip) {
        swap(leftBits, rightBits);
    }

    if (at == ZERO_EXTEND) {
        for (int i = var.bitnum() - leftBits - 1; i >= rightBits; i--) {
            var.set(i, bddManager.bddZero());
        }
    } else if (at == SIGN_EXTEND && rightBits != 0) {
        for (unsigned int i = rightBits; i < var.bitnum() - leftBits; i++) {
            var.set(i, var[i - 1]);
        }
    } else if (at == SIGN_EXTEND && rightBits == 0) {
        // when does this happen if newBitWidth is always even non zero number? BW = -1
        for (int i = var.bitnum() - leftBits - 1; i >= 0; i--) {
            var.set(i, var[i + 1]);
        }
    }

    return { var, PRECISE, APPROXIMATED };
}

Approximated<Bvec> ExprToBDDTransformer::getBvecFromExpr(const expr &e, const vector<boundVar> &boundVars)
{
    assert(e.is_bv());
    if (Solver::resultComputed) return {Bvec::bvec_con(bddManager, e.get_sort().bv_size(), 0), APPROXIMATED};
    if (DEBUG) {
        Solver::m_z3context.lock();
        std::string exprString = e.to_string();
        Solver::m_z3context.unlock();
        std::cout << exprString << std::endl;
    }
    

    auto cachedExpr = caches.foundExprInCaches(e, boundVars);
    if (cachedExpr.has_value()) {
        //std::cout <<   " Found in cache!!!" << std::endl;
        return cachedExpr.value();
    }

    if (e.is_var()) {
        return getVar(e, boundVars);

    } else if (e.is_numeral()) {
        return caches.insertIntoCaches(e, { getNumeralBvec(e), PRECISE }, boundVars);
    } else if (e.is_const()) {
        return getConst(e, boundVars);
    } else if (e.is_app()) {
        func_decl f = e.decl();
        auto decl_kind = f.decl_kind();

        if (decl_kind == Z3_OP_BADD) {
            return getAddition(e, boundVars);
        } else if (decl_kind == Z3_OP_BSUB) {
            return getSubstraction(e, boundVars);
        } else if (decl_kind == Z3_OP_BSHL) {
            return getShiftLeft(e, boundVars);
        } else if (decl_kind == Z3_OP_BLSHR) {
            return getShiftRight(e, boundVars);
        } else if (decl_kind == Z3_OP_BASHR) {
            auto bitwidth = e.get_sort().bv_size();
            if (e.arg(1).is_numeral()) {
                return bvec_unOp(
                        e, [&](auto x) { return x.bvec_shrfixed(getNumeralValue(e.arg(1)), x[bitwidth - 1]); }, boundVars);
            } else {
                return bvec_binOp(
                        e, [&](auto x, auto y) { return Bvec::bvec_shr(x, y, x[bitwidth - 1]); }, boundVars);
            }
        } else if (decl_kind == Z3_OP_CONCAT) {
            return getConcat(e, boundVars);
        } else if (decl_kind == Z3_OP_EXTRACT) {
            return getExtract(e, boundVars);

        } else if (decl_kind == Z3_OP_BNOT) {
            return getBNot(e, boundVars);
        } else if (decl_kind == Z3_OP_BNEG) {
            return getBNeg(e, boundVars);
            
        } else if (decl_kind == Z3_OP_BOR) {
            return getBOr(e, boundVars);
        } else if (decl_kind == Z3_OP_BAND) {
            return getBAnd(e, boundVars);
        } else if (decl_kind == Z3_OP_BXOR) {
            return getBXor(e, boundVars);
        } else if (decl_kind == Z3_OP_BMUL) {
            return getMul(e, boundVars);
        } else if (decl_kind == Z3_OP_BUREM || decl_kind == Z3_OP_BUREM_I || decl_kind == Z3_OP_BUDIV || decl_kind == Z3_OP_BUDIV_I) {
            // I at the end is operation that assumes that second operand is non-zero
            return getDivOrRem(e, boundVars);
        } else if (decl_kind == Z3_OP_BSDIV || decl_kind == Z3_OP_BSDIV_I) {
            return getSignedDivRem(e, boundVars, udiv);

        } else if (decl_kind == Z3_OP_BSREM || decl_kind == Z3_OP_BSREM_I) {
            
            return getSignedDivRem(e, boundVars, urem);
        } else if (decl_kind == Z3_OP_ITE) {
            return getIte(e, boundVars);
        } else {
            cout << "ERROR: not supported function " << e << endl;
            cout << "unknown";
            exit(0);
        }
    }

    cout << "bvec else" << e << endl;
    abort();
}

unsigned int ExprToBDDTransformer::getNumeralValue(const expr &e) const
{
    std::unique_lock<std::mutex> lk(Solver::m_z3context);
    return HexHelper::get_numeral_value(e.to_string());
}

Bvec ExprToBDDTransformer::getNumeralBvec(const z3::expr &e)
{
    z3::sort s = e.get_sort();

    std::string numeralString;
    {
        std::lock_guard<std::mutex> lg(Solver::m_z3context);
        numeralString = e.to_string();
    }

    int bitSize = s.bv_size();
    const string prefix = numeralString.substr(0, 2);
    string valueString = numeralString.substr(2);

    assert(prefix == "#x" || prefix == "#b");

    Bvec toReturn = Bvec::bvec_false(bddManager, bitSize);
    if (prefix == "#x") {
        valueString = HexHelper::hex_str_to_bin_str(valueString);
    }

    int i = valueString.size();
    for (const char &c : valueString) {
        i--;
        toReturn.set(i, c == '1' ? bddManager.bddOne() : bddManager.bddZero());
    }

    return toReturn;
}

BDD ExprToBDDTransformer::Proccess()
{
    approximation = NO_APPROXIMATION;
    config.approximationMethod = NONE;
    variableBitWidth = 0;

    if (expression.is_app() && expression.decl().decl_kind() == Z3_OP_TRUE) {
        return bddManager.bddOne();
    } else if (expression.is_app() && expression.decl().decl_kind() == Z3_OP_FALSE) {
        return bddManager.bddZero();
    }

    return loadBDDsFromExpr(expression).upper;
}

BDDInterval ExprToBDDTransformer::ProcessUnderapproximation(int bitWidth, unsigned int precision)
{
    approximation = UNDERAPPROXIMATION;
    variableBitWidth = bitWidth;
    operationPrecision = precision;

    return loadBDDsFromExpr(expression);
}

BDDInterval ExprToBDDTransformer::ProcessOverapproximation(int bitWidth, unsigned int precision)
{
    approximation = OVERAPPROXIMATION;
    variableBitWidth = bitWidth;
    operationPrecision = precision;

    return loadBDDsFromExpr(expression);
}

BDDInterval ExprToBDDTransformer::bvec_ule(Bvec &arg0, Bvec &arg1, bool isPositive)
{
    if (config.approximationMethod == OPERATIONS || config.approximationMethod == BOTH) {
        auto over = Bvec::bvec_lte_overApprox(arg0, arg1);
        auto under = Bvec::bvec_lte_underApprox(arg0, arg1) |
                Bvec::bvec_equ_underApprox(arg0, Bvec::bvec_false(bddManager, arg0.bitnum())) |
                Bvec::bvec_equ_underApprox(arg1, Bvec::bvec_true(bddManager, arg1.bitnum()));

        return isPositive ? BDDInterval(over, under) : BDDInterval(under, over);
    }

    return BDDInterval{ Bvec::bvec_lte(arg0, arg1).GetBDD(bddManager.bddZero()) };
    ;
}

BDDInterval ExprToBDDTransformer::bvec_ult(Bvec &arg0, Bvec &arg1, bool isPositive)
{
    BDDInterval result;

    if (config.approximationMethod == OPERATIONS || config.approximationMethod == BOTH) {
        auto over = Bvec::bvec_lth_overApprox(arg0, arg1) &
                Bvec::bvec_nequ_overApprox(arg0, Bvec::bvec_true(bddManager, arg0.bitnum())) &
                Bvec::bvec_nequ_overApprox(arg1, Bvec::bvec_false(bddManager, arg1.bitnum()));
        auto under = Bvec::bvec_lth_underApprox(arg0, arg1);

        return isPositive ? BDDInterval(over, under) : BDDInterval(under, over);
    }

    return BDDInterval{ Bvec::bvec_lth(arg0, arg1).GetBDD(bddManager.bddZero()) };
}

// @pre: e.num_args() > 0
// @pre: op is associative
Approximated<Bvec> ExprToBDDTransformer::bvec_assocOp(const z3::expr &e, const std::function<Bvec(Bvec, Bvec)> &op, const std::vector<boundVar> &boundVars)
{
    unsigned num = e.num_args();
    auto toReturn = getBvecFromExpr(e.arg(0), boundVars);
    for (unsigned int i = 1; i < num; i++) {
        toReturn = toReturn.Apply2<Bvec>(getBvecFromExpr(e.arg(i), boundVars), op);
    }

    return caches.insertIntoCaches(e, toReturn, boundVars);
}



Approximated<Bvec> ExprToBDDTransformer::bvec_assocOpApprox(const z3::expr &e, const std::function<Bvec(Bvec, Bvec, std::vector<Interval>)> &op, 
                                                                const std::function<std::vector<Interval>(std::vector<Interval>,std::vector<Interval>)>& intervalOp,
                                                                const std::vector<boundVar> &boundVars)
{
    unsigned num = e.num_args();
    auto result = getBvecFromExpr(e.arg(0), boundVars);
    auto resInterval = caches.findInterval(e.arg(0));
    for (unsigned int i = 1; i < num; i++) {
        auto bvec2 = getBvecFromExpr(e.arg(1), boundVars);
        resInterval= intervalOp(resInterval, caches.findInterval(e.arg(1)));
        result = result.Apply2<Bvec>(bvec2, op,resInterval);
    }
    caches.insertInterval(e, resInterval);
    return caches.insertIntoCaches(e, result, boundVars);
}

/// @brief  Binary operations with approximated variables. Finds resulting bvec computed for lower bit width and uses it for further computation.
/// @param e 
/// @param op 
/// @param boundVars 
/// @return computed bitvector
Approximated<Bvec> ExprToBDDTransformer::bvec_binaryOpApprox(const z3::expr &e, const std::function<Bvec(Bvec, Bvec, std::vector<Interval>)> &op, 
                                                                const std::function<std::vector<Interval>(std::vector<Interval>,std::vector<Interval>)>& intervalOp,
                                                                const std::vector<boundVar> &boundVars)
{
    
    assert(e.num_args() == 2);
    auto bvec1 = getBvecFromExpr(e.arg(0), boundVars);
    auto bvec2 = getBvecFromExpr(e.arg(1), boundVars);
    auto resInterval= intervalOp(caches.findInterval(e.arg(0)), caches.findInterval(e.arg(1)));
    caches.insertInterval(e,resInterval );
    auto result = bvec1.Apply2<Bvec>(bvec2, op,resInterval); 
    return caches.insertIntoCaches(e, result, boundVars);
}

Approximated<Bvec> ExprToBDDTransformer::bvec_binOp(const z3::expr &e, const std::function<Bvec(Bvec, Bvec)> &op, const std::vector<boundVar> &boundVars)
{
    auto result = getBvecFromExpr(e.arg(0), boundVars).Apply2<Bvec>(getBvecFromExpr(e.arg(1), boundVars), op);

    return caches.insertIntoCaches(e, result, boundVars);
}

Approximated<Bvec> ExprToBDDTransformer::bvec_unOp(const z3::expr &e, const std::function<Bvec(Bvec)> &op, const std::vector<boundVar> &boundVars)
{
    auto result = getBvecFromExpr(e.arg(0), boundVars).Apply<Bvec>(op);

    return caches.insertIntoCaches(e, result, boundVars);
}

Approximated<Bvec> ExprToBDDTransformer::bvec_unOpApprox(const z3::expr &e, const std::function<Bvec(Bvec, std::vector<Interval>)> &op,
                                                         const std::function<std::vector<Interval>(std::vector<Interval>)>& intervalOp, 
                                                         const std::vector<boundVar> &boundVars)
{
    auto child = getBvecFromExpr(e.arg(0), boundVars);
    auto resInterval = intervalOp(caches.findInterval(e.arg(0)));
    caches.insertInterval(e, resInterval);
    auto result = child.Apply<Bvec>(op, resInterval);
    return caches.insertIntoCaches(e, result, boundVars);
}

bool ExprToBDDTransformer::isMinusOne(const Bvec &bvec)
{
    return std::all_of(bvec.m_bitvec.begin(), bvec.m_bitvec.end(), [](auto &bit) { return bit.IsOne(); });
}



////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////// GET BVECS FUNCTIONS ////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

///////////////////////////  Help Functions ///////////////////////////////////////////////////////////////////////////////////////////////////////////////
Bvec ExprToBDDTransformer::bvec_mul(Bvec &arg0, Bvec &arg1, Computation_state &state)
{
    unsigned int bitNum = arg0.bitnum();

    if (isMinusOne(arg0)) {
        Bvec::arithmetic_neg(arg1);
    } else if (isMinusOne(arg1)) {
        Bvec::arithmetic_neg(arg0);
    }

    Bvec result(bddManager);
    if (arg0.bitnum() <= 32 && arg1.bitnum() <= 32) {
        if (arg1.bvec_isConst()) {
            swap(arg0, arg1);
        }

        if (arg0.bvec_isConst()) {
            unsigned int val = arg0.bvec_val();

            unsigned int largestDividingTwoPower = 0;
            for (int i = 0; i < 64; i++) {
                if (val % 2 == 0) {
                    largestDividingTwoPower++;
                    val = val >> 1;
                }
            }

            if (largestDividingTwoPower > 0) {
                result = (arg1 * val) << largestDividingTwoPower;
                return result;
            }

            if (val <= INT_MAX) {
                return arg1 * val;
            }
        }
    }

    int leftConstantCount = 0;
    int rightConstantCount = 0;

    for (unsigned int i = 0; i < arg0.bitnum(); i++) {
        if (arg0[i].IsZero() || arg0[i].IsOne()) {
            leftConstantCount++;
        }

        if (arg1[i].IsZero() || arg1[i].IsOne()) {
            rightConstantCount++;
        }
    }

    if (leftConstantCount < rightConstantCount) {
        swap(arg0, arg1);
    }

    if ( ApproximateOps() ){
        return Bvec::bvec_mul_nodeLimit_state(arg0, arg1, precisionMultiplier * operationPrecision, state).bvec_coerce(bitNum);
    } else if (ApproximateVars()) {
        unsigned int nodeLimit = (config.approximationMethod == BOTH) ? precisionMultiplier * operationPrecision : UINT_MAX;
        return  Bvec::bvec_mul_nodeLimit(arg0, arg1, nodeLimit).bvec_coerce(bitNum);
    }
    return Bvec::bvec_mul(arg0, arg1).bvec_coerce(bitNum);
}

bool ExprToBDDTransformer::ApproximateOps() const
{   
    return operationPrecision != 0 && 
        ( (config.approximationMethod == BOTH && incrementedApproxStyle == PRECISION ) || (config.approximationMethod == OPERATIONS));
}

bool ExprToBDDTransformer::ApproximateVars() const
{
    return (true && (config.approximationMethod == VARIABLES  || (config.approximationMethod == BOTH && incrementedApproxStyle == BIT_WIDTH )));
}



bool ExprToBDDTransformer::shouldApproximateVar(const boundVar &bVar) const
{
    return ( (config.approximationMethod == VARIABLES  || config.approximationMethod == BOTH) &&
            ((bVar.second == EXISTENTIAL && approximation == UNDERAPPROXIMATION) ||
                    (bVar.second == UNIVERSAL && approximation == OVERAPPROXIMATION)));
}


// num is positive iff shift left (if negative, then shift right)
Approximated<Bvec> ExprToBDDTransformer::shiftNumeral(const expr &e, const vector<boundVar> &boundVars, int num) {
    if (ApproximateVars()){
        auto prevBvec = caches.findPrevBWPreciseBvec(e, boundVars);
        if (prevBvec.has_value()) {
            auto res =  bvec_unOpApprox(e, [&](auto x,  std::vector<Interval> changeInterval ) 
            { return Bvec::bvec_update_shifted(x, changeInterval,  num, prevBvec.value().value); },
              [&](auto x) {return BWChangeEffect::EffectOfShift(x, num );},boundVars);
              
                if (DEBUG) {
                    BvecTester::testBvecEq(res,(num > 0)? bvec_unOp(
                    e, [&](auto x) { return x << num ; }, boundVars) : bvec_unOp(
                    e, [&](auto x) { return x >> -num; }, boundVars) );
                }
                return res;

        }
    }
    if (num >= 0) {
		return bvec_unOp(
                e, [&](auto x) { return x << num ; }, boundVars);
	} else {
		return bvec_unOp(
            e, [&](auto x) { return x >> -num; }, boundVars);
	}
}

void ExprToBDDTransformer::checkEqual(const Approximated<Bvec>& approxRes, const std::function<Approximated<Bvec>()> &op) {
    if (DEBUG) {
        BvecTester::testBvecEq(approxRes, op());
    }
}

void ExprToBDDTransformer::checkEqual(const Approximated<Bvec>& approxRes, const Approximated<Bvec>& orig) {
    if (DEBUG) {
        BvecTester::testBvecEq(approxRes, orig);
    }
}
///////////////////////////  Functions called in ExprToBDDTransformer::getBvecFromExpr /////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

Approximated<Bvec> ExprToBDDTransformer::getVar(const expr &e, const vector<boundVar> &boundVars)
{
    Z3_ast ast = (Z3_ast) e;
    int deBruijnIndex = Z3_get_index_value(*context, ast);
    boundVar bVar = boundVars[boundVars.size() - deBruijnIndex - 1];

    if (shouldApproximateVar(bVar)) {
        caches.insertInterval(e, BWChangeEffect::EffectOnVar(variableBitWidth, vars.at(bVar.first).bitnum(), operationPrecision) ); // latter arg is number of bits of the var
        auto res = getApproximatedVariable(bVar.first, variableBitWidth, approximationType);
        return caches.insertIntoCaches(e,res, boundVars);
    }
    return caches.insertIntoCaches(e, { vars.at(bVar.first), PRECISE }, boundVars);
}

Approximated<Bvec> ExprToBDDTransformer::getConst(const expr &e, const vector<boundVar> &boundVars)
{
    Bvec result(bddManager);
    if ((config.approximationMethod == VARIABLES  || config.approximationMethod == BOTH)  && approximation == UNDERAPPROXIMATION) {
        std::unique_lock<std::mutex> lk(Solver::m_z3context);
        const std::string expressionString = e.to_string();

        caches.insertInterval(e, BWChangeEffect::EffectOnVar(variableBitWidth, vars.at(expressionString).bitnum(),operationPrecision) );
        auto result = getApproximatedVariable(expressionString, variableBitWidth, approximationType);
        return caches.insertIntoCaches(e, result, boundVars);
    }
    std::unique_lock<std::mutex> lk(Solver::m_z3context);
    return caches.insertIntoCaches(e, { vars.at(e.to_string()), PRECISE }, boundVars);
}



Approximated<Bvec> ExprToBDDTransformer::getShiftLeft(const expr &e, const vector<boundVar> &boundVars){
    if (e.arg(1).is_numeral()) {
        return shiftNumeral(e, boundVars, getNumeralValue(e.arg(1)));
    } else {
        return bvec_binOp(
                e, [](auto x, auto y) { return x << y; }, boundVars);
    }
}

Approximated<Bvec> ExprToBDDTransformer::getShiftRight(const expr &e, const vector<boundVar> &boundVars){
    if (e.arg(1).is_numeral()) {
         return shiftNumeral(e, boundVars, -getNumeralValue(e.arg(1)));
    } else {
        return bvec_binOp(
                e, [](auto x, auto y) { return x >> y; }, boundVars);
    }
}


Approximated<Bvec> ExprToBDDTransformer::getBNot(const expr &e, const vector<boundVar> &boundVars)
{
    if (ApproximateVars()) {

        auto prevBvec = caches.findPrevBWPreciseBvec(e, boundVars);
        if ( prevBvec.has_value()){
            auto res =  bvec_unOpApprox( e,
            [&](auto x , std::vector<Interval> changeInterval ) { return Bvec::bvec_map1_prev(x,changeInterval, [&](const MaybeBDD &a) { return !a; }, prevBvec.value().value); },
            [&](auto x) {return BWChangeEffect::EffectOnKid(x);}, 
            boundVars); // same effect (interval) as on child
            //checkEqual(res,[&]() {return bvec_unOp(e, std::bind(Bvec::bvec_map1, _1, [&](const MaybeBDD &a) { return !a; }), boundVars);}  ); //tests res if DEBUG == true
            return res;
        }  
    }
    return bvec_unOp(e, std::bind(Bvec::bvec_map1, _1, [&](const MaybeBDD &a) { return !a; }), boundVars);
}

Approximated<Bvec> ExprToBDDTransformer::getBNeg(const expr &e, const vector<boundVar> &boundVars)
{
    if (ApproximateVars()) {
        auto prevBvec = caches.findPrevBWPreciseBvec(e, boundVars);
        auto prevBvecState = Caches::getstateFromBvec(prevBvec);
        if (prevBvec.has_value()){
            auto result =  bvec_unOpApprox( e,
            [&](auto x , std::vector<Interval> changeInterval ) { return Bvec::arithmetic_neg_prev(x,changeInterval, prevBvecState); },
            [&](auto x) {return BWChangeEffect::EffectFromLeastSignChangedBit(x);}, 
            boundVars); 
            // checkEqual(result,  [&] () {return bvec_unOp(
            //         e, [&](auto x) { return Bvec::arithmetic_neg(x); }, boundVars);});
            
            return result;
        }  
    }
    return bvec_unOp(
                    e, [&](auto x) { return Bvec::arithmetic_neg(x); }, boundVars);
}

Approximated<Bvec> ExprToBDDTransformer::getBOr(const expr &e, const vector<boundVar> &boundVars) {
    
    if ( ApproximateVars()) {
        auto prevBvec = caches.findPrevBWPreciseBvec(e, boundVars);
        if (prevBvec.has_value()) {
            auto res = bvec_assocOpApprox(
            e, [&](auto x, auto y , std::vector<Interval> changeInterval ) 
            { return Bvec::bvec_map2_prev(x, y,changeInterval, [&](const MaybeBDD &a, const MaybeBDD &b) { return a | b; },  prevBvec.value().value); },
                [](auto x, auto y) {return BWChangeEffect::EffectOfUnion(x, y);},boundVars);
            // checkEqual(res, [&](){return bvec_assocOp(
            //         e, [&](const Bvec &a, const Bvec &b) { return a | b; }, boundVars);});
            return res;
        }
        
    }
    return bvec_assocOp(
                    e, [&](const Bvec &a, const Bvec &b) { return a | b; }, boundVars);
}

Approximated<Bvec> ExprToBDDTransformer::getBAnd(const expr &e, const vector<boundVar> &boundVars) {
    if (ApproximateVars()) {
        auto prevBvec = caches.findPrevBWPreciseBvec(e, boundVars);
        if (prevBvec.has_value()) {
            auto res = bvec_assocOpApprox(
            e, [&](auto x, auto y , std::vector<Interval> changeInterval ) 
            { return Bvec::bvec_map2_prev(x, y,changeInterval, [&](const MaybeBDD &a, const MaybeBDD &b) { return a & b; },  prevBvec.value().value); },
                [](auto x, auto y) {return BWChangeEffect::EffectOfUnion(x, y);},boundVars);
            // checkEqual(res, [&](){return bvec_assocOp(
            //         e, [&](const Bvec &a, const Bvec &b) { return a & b; }, boundVars);});
            return res;
        }
        
    }
    return bvec_assocOp(
                    e, [&](const Bvec &a, const Bvec &b) { return a & b; }, boundVars);
}

Approximated<Bvec> ExprToBDDTransformer::getBXor(const expr &e, const vector<boundVar> &boundVars) {
    if (ApproximateVars()) {
        auto prevBvec = caches.findPrevBWPreciseBvec(e, boundVars);
        if (prevBvec.has_value()) {
            auto res = bvec_assocOpApprox(
            e, [&](auto x, auto y , std::vector<Interval> changeInterval ) 
            { return Bvec::bvec_map2_prev(x, y,changeInterval, [&](const MaybeBDD &a, const MaybeBDD &b) { return a ^ b; },  prevBvec.value().value); },
                [](auto x, auto y) {return BWChangeEffect::EffectOfUnion(x, y);},boundVars);
            // checkEqual(res, [&]() {return bvec_assocOp(
            //         e, [&](const Bvec &a, const Bvec &b) { return a ^ b; }, boundVars);});
            return res;
        }
        
    }
    return bvec_assocOp(
                    e, [&](const Bvec &a, const Bvec &b) { return a ^ b; }, boundVars);
}

Approximated<Bvec> ExprToBDDTransformer::getAddition(const expr &e, const vector<boundVar> &boundVars)
{
    if (ApproximateOps()) {
        auto state = caches.findStateInCaches(e, boundVars);
        bool createdFreshState = state.IsFresh();
        auto res = bvec_assocOp(
                e, [&](auto x, auto y) { return Bvec::bvec_add_nodeLimit(x, y, precisionMultiplier * operationPrecision, state); }, boundVars);

        caches.insertStateIntoCaches(e, state, boundVars, res, createdFreshState);
        
        return res;
    } else if (ApproximateVars()) {
        
        auto prevBvecState = Caches::getstateFromBvec(caches.findPrevBWPreciseBvec(e, boundVars));
        unsigned int nodeLimit = (config.approximationMethod == BOTH) ? precisionMultiplier * operationPrecision : UINT_MAX;
        
        auto res = bvec_assocOpApprox(
            e, [&](auto x, auto y , std::vector<Interval> changeInterval ) 
            { return Bvec::bvec_add_prev(x, y,changeInterval, prevBvecState, nodeLimit); },
                [](auto x, auto y) {return BWChangeEffect::EffectOnAddorSub(x, y);},boundVars);
        
        

        caches.insertStateIntoCaches(e, prevBvecState, boundVars, res, true); // always creating new state that is not in state cache
    
        if (DEBUG) {
            BvecTester::testAddOrSub(res, bvec_assocOp(
            e, [&](auto x, auto y) { return Bvec::bvec_add_nodeLimit(x,y, nodeLimit); }, boundVars), prevBvecState);

        }
        return res; 
    }
    return bvec_assocOp(
            e, [&](auto x, auto y) { return x + y; }, boundVars);
}

Approximated<Bvec> ExprToBDDTransformer::getSubstraction(const expr &e, const vector<boundVar> &boundVars)
{
    checkNumberOfArguments<2>(e);
    if (ApproximateOps()) {
        auto state = caches.findStateInCaches(e, boundVars);
        bool createdFreshState = state.IsFresh();
        auto res = bvec_assocOp(
                e, [&](auto x, auto y) { return Bvec::bvec_sub(x, y, precisionMultiplier * operationPrecision, state); }, boundVars);

        caches.insertStateIntoCaches(e, state, boundVars, res, createdFreshState);
        return res;
    } else if (ApproximateVars())
    {
        auto prevBvecState = Caches::getstateFromBvec(caches.findPrevBWPreciseBvec(e, boundVars));
        unsigned int nodeLimit = (config.approximationMethod == BOTH) ? precisionMultiplier * operationPrecision : INT_MAX;
        
        auto res = bvec_assocOpApprox(
            e, [&](auto x, auto y , std::vector<Interval> changeInterval ) 
            { return Bvec::bvec_sub_prev(x, y,changeInterval, prevBvecState, nodeLimit); },
                [](auto x, auto y) {return BWChangeEffect::EffectOnAddorSub(x, y);},boundVars);
        caches.insertStateIntoCaches(e, prevBvecState, boundVars, res, true); // always creating new state that is not in state cache
        if (DEBUG) {
            BvecTester::testAddOrSub(res, bvec_assocOp(
            e, [&](auto x, auto y) { return x - y; }, boundVars), prevBvecState);
        }
        return res; 
    }
    return bvec_binOp(
            e, [](auto x, auto y) { return x - y; }, boundVars);
}

Approximated<Bvec>  ExprToBDDTransformer::getCurrentBvec(const expr &e, const vector<boundVar> &boundVars, int newSize, bool& wasCurrentCached) {
    if ( true &&ApproximateVars() ){
        auto prevBvec = caches.findPrevBWPreciseBvec(e, boundVars);
        if ( prevBvec.has_value() ) {
            //std::cout << "Number of items in prevBWpreciseBvecs cahce "  << caches.prevBWpreciseBvecs.size() << std::endl;
            wasCurrentCached = true;
            return prevBvec.value();
        }
    }
    wasCurrentCached = false;
    return {Bvec::bvec_false(bddManager, newSize), PRECISE, PRECISE};
}

Bvec ExprToBDDTransformer::computeConcat(const expr &expr_arg,  Bvec currentBvec, const Bvec& arg, int offset, int newSize, bool wasCurrentCached, std::vector<Interval>& currentInterval ) {
    if( wasCurrentCached) {
        auto kidInterval = caches.findInterval(expr_arg);
        kidInterval = BWChangeEffect::EffectOnExtract(kidInterval, 0, arg.m_bitvec.size() );
        kidInterval = BWChangeEffect::ShiftLeft(kidInterval, offset);
        if (DEBUG) {
            std::cout << "Compute concat: new size = " << newSize <<  " current bvec size" << currentBvec.m_bitvec.size() << " offset=" << offset <<std::endl;
            std::cout << "Kid expr: " << expr_arg.to_string()  << " Kid size = " << arg.m_bitvec.size()<< std::endl;
            std::cout << "kid interval" << std::endl;
            
            for(auto i : kidInterval) {
                std::cout << "[ " << i.first << ", " << i.second << "]" << std::endl;
            }
        }
        currentBvec = Bvec::bvec_update_shiftedConcat(arg, kidInterval, offset,currentBvec );
        if (DEBUG) {
            for (int i = 0; i < arg.m_bitvec.size(); ++i) {
                    assert(arg.m_bitvec[i].Equals(currentBvec.m_bitvec[i + offset]));
                }
        }
        return currentBvec;
    } else {
        
        return Bvec::bvec_map2(currentBvec,
                arg.bvec_coerce(newSize) << offset,
                [&](const MaybeBDD &a, const MaybeBDD &b) { return a ^ b; });
    }
}


Approximated<Bvec> ExprToBDDTransformer::getConcat(const expr &e, const vector<boundVar> &boundVars )
{
    func_decl f = e.decl();
    unsigned num = e.num_args();
    int newSize = f.range().bv_size();
    int offset = 0;
    std::vector<Interval> currentInterval = {};    // nothing to recompte
    bool wasCurrentCached;
    auto  [currentBvec, opPrecision, varPrecision] = getCurrentBvec(e, boundVars, newSize, wasCurrentCached);  
    assert(num > 0);
    for (int i = num - 1; i >= 0; i--) {
        auto [arg, argOpPrecision, argVarPrecision] = getBvecFromExpr(e.arg(i), boundVars);
        currentBvec = computeConcat( e.arg(i),currentBvec,  arg,  offset,  newSize,  wasCurrentCached,  currentInterval);
        opPrecision = opPrecision && argOpPrecision;
        varPrecision = varPrecision && argVarPrecision;
        offset += f.domain(i).bv_size();
    }
    return caches.insertIntoCaches(e, { currentBvec, opPrecision, varPrecision }, boundVars);
}

Approximated<Bvec> ExprToBDDTransformer::getExtractBvec(const expr &e, const vector<boundVar> &boundVars, int bitFrom,int extractBits ) 
{
    if (true && ApproximateVars()){ 
        auto prevBvec = caches.findPrevBWPreciseBvec(e, boundVars);
        if (prevBvec.has_value()) {
            auto res =  bvec_unOpApprox(e, [&](auto x,  std::vector<Interval> changeInterval ) 
            { return Bvec::bvec_update_shifted(x, changeInterval,  -bitFrom, prevBvec.value().value); },
              [&](auto x) {return BWChangeEffect::EffectOnExtract(x,bitFrom, extractBits );},boundVars);
            if (DEBUG) {
                BvecTester::testBvecSize( extractBits,res);
                checkEqual(res, [&](){return bvec_unOp(
            e,
            [&](auto x) { return x
                                  .bvec_shrfixed(bitFrom, MaybeBDD(bddManager.bddZero()))
                                  .bvec_coerce(extractBits); },
            boundVars);});
            }
            return res;
        }            
    } 
    return bvec_unOp(
            e,
            [&](auto x) { return x
                                  .bvec_shrfixed(bitFrom, MaybeBDD(bddManager.bddZero()))
                                  .bvec_coerce(extractBits); },
            boundVars);


}

Approximated<Bvec> ExprToBDDTransformer::getExtract(const expr &e, const vector<boundVar> &boundVars)
{
    Z3_func_decl z3decl = (Z3_func_decl) e.decl();
    int bitTo = Z3_get_decl_int_parameter(*context, z3decl, 0);
    int bitFrom = Z3_get_decl_int_parameter(*context, z3decl, 1);
    int extractBits = bitTo - bitFrom + 1;
    return getExtractBvec(e, boundVars, bitFrom, extractBits);
}

Approximated<Bvec> ExprToBDDTransformer::getMul(const expr &e, const vector<boundVar> &boundVars)
{
    checkNumberOfArguments<2>(e);   // in preprocessing adjusted so that mul has always 2 args

    auto state = caches.findStateInCaches(e, boundVars);
    bool createdFreshState = state.IsFresh();
    auto res = bvec_assocOp(
            e, [&](auto x, auto y) { return bvec_mul(x, y, state); }, boundVars);
    caches.insertStateIntoCaches(e, state, boundVars, res, createdFreshState);
    return res;
}

Approximated<Bvec> ExprToBDDTransformer::getDivOrRem(const expr &e, const vector<boundVar> &boundVars)
{
    checkNumberOfArguments<2>(e);
    func_decl f = e.decl();
    auto decl_kind = f.decl_kind();
    Bvec div = Bvec::bvec_false(bddManager, e.decl().range().bv_size());
    Bvec rem = Bvec::bvec_false(bddManager, e.decl().range().bv_size());
    auto [arg0, arg0OpPrecision, arg0VarPrecision] = getBvecFromExpr(e.arg(0), boundVars);
    auto [arg1, arg1OpPrecision, arg1VarPrecision] = getBvecFromExpr(e.arg(1), boundVars);

    Precision opPrecision = arg0OpPrecision && arg1OpPrecision;
    Precision varPrecision = arg0VarPrecision && arg1VarPrecision;

    int result = 0;
    if (e.arg(1).is_numeral() && e.get_sort().bv_size() <= 32) {
        result = arg0.bvec_divfixed(getNumeralValue(e.arg(1)), div, rem);
    } else if ((config.approximationMethod == OPERATIONS || config.approximationMethod == BOTH) &&
            operationPrecision != 0) {
        auto state = caches.findStateInCaches(e, boundVars);
        bool createdFreshState = state.IsFresh();
        result = Bvec::bvec_div_nodeLimit(arg0, arg1, div, rem, precisionMultiplier * operationPrecision, state);
        if (result == 0) {
            caches.insertStateIntoCaches(e, state, boundVars, { decl_kind == Z3_OP_BUDIV || decl_kind == Z3_OP_BUDIV_I ? div : rem, opPrecision, varPrecision }, createdFreshState);
        }
    } else {
        result = arg0.bvec_div(arg0, arg1, div, rem);
    }

    if (result == 0) {
        return caches.insertIntoCaches(e, { decl_kind == Z3_OP_BUDIV || decl_kind == Z3_OP_BUDIV_I ? div : rem, opPrecision, varPrecision }, boundVars);
    } else {
        cout << "ERROR: division error" << endl;
        cout << "unknown";
        exit(0);
    }
}

expr ExprToBDDTransformer::getLastItePart(const expr &e, expr (*op)(const expr &e1, const expr &e2),
                                          const expr &arg0, const expr &arg1, const expr &zero, const expr &one,
                                          const expr &msb_s, const expr &msb_t ) const{
    func_decl f = e.decl();
    auto decl_kind = f.decl_kind();
    if (decl_kind == Z3_OP_BSDIV || decl_kind == Z3_OP_BSDIV_I) {
        return ite(msb_s == zero && msb_t == one,
                            -op(arg0, -arg1),
                            op(-arg0, -arg1));
    } else {
        // urem or urem_i
        return ite(msb_s == zero && msb_t == one,
                            op(arg0, -arg1),
                            -op(-arg0, -arg1));
    }
}

Approximated<Bvec> ExprToBDDTransformer::getSignedDivRem(const expr &e, const vector<boundVar> &boundVars, expr (*op)(const expr &e1, const expr &e2))
{
    checkNumberOfArguments<2>(e);

    expr arg0 = e.arg(0);
    expr arg1 = e.arg(1);

    expr zero = context->bv_val(0, 1);
    expr one = context->bv_val(1, 1);

    int size = e.arg(0).get_sort().bv_size();
    expr msb_s = arg0.extract(size - 1, size - 1);
    expr msb_t = arg1.extract(size - 1, size - 1);
    expr last_ite = getLastItePart(e, op, arg0, arg1, zero, one,msb_s, msb_t );
    expr ex = ite(msb_s == zero && msb_t == zero,
            op(arg0, arg1),
            ite(msb_s == one && msb_t == zero,
                    -op(-arg0, arg1),
                    last_ite));

    caches.clearCaches(); // why?
    auto result = getBvecFromExpr(ex, boundVars);
    return caches.insertIntoCaches(ex, result, boundVars);
}

Approximated<Bvec> ExprToBDDTransformer::getIte(const expr &e, const vector<boundVar> &boundVars)
{
    checkNumberOfArguments<3>(e);

    //TODO: Tohle může být nekorektní kvůli isPositive!!!
    auto arg0 = getBDDFromExpr(e.arg(0), boundVars, false, true);
    if (arg0.upper != arg0.lower) {
        auto unknown = Bvec{ bddManager,
            e.get_sort().bv_size(),
            MaybeBDD{} };
        return caches.insertIntoCaches(e, { unknown, APPROXIMATED, APPROXIMATED }, boundVars);
    }

    Bvec result(bddManager);

    if (config.lazyEvaluation && arg0.lower.IsOne()) {
        result = getBvecFromExpr(e.arg(1), boundVars).value;
    } else if (config.lazyEvaluation && arg0.upper.IsZero()) {
        result = getBvecFromExpr(e.arg(2), boundVars).value;
    } else {
        auto arg1 = getBvecFromExpr(e.arg(1), boundVars).value;
        auto arg2 = getBvecFromExpr(e.arg(2), boundVars).value;
        auto maybeArg0 = MaybeBDD(arg0.upper);

        if (false &&ApproximateOps() ) {
            auto state = caches.findStateInCaches(e, boundVars);
            bool createdFreshState = state.IsFresh();
            result = Bvec::bvec_ite(MaybeBDD{ maybeArg0 }, arg1, arg2, precisionMultiplier * operationPrecision, state);
            caches.insertStateIntoCaches(e, state, boundVars, { result, APPROXIMATED, APPROXIMATED }, createdFreshState);
        } else {
            result = Bvec::bvec_ite(MaybeBDD{ maybeArg0 },
                    arg1,
                    arg2);
        }
    }

    return caches.insertIntoCaches(e, { result, APPROXIMATED, APPROXIMATED }, boundVars);
}

//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////// UTILS /////////////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

bool ExprToBDDTransformer::isInterrupted()
{
    return Solver::resultComputed;
}

template <typename T, typename TorderFunc>
void ExprToBDDTransformer::sortVec(std::vector<T> &vec, TorderFunc &&orderExpr)
{
    std::sort(vec.begin(), vec.end(), [&](const auto &a, const auto &b) -> bool {
        return orderExpr(a, b);
    });
}

void ExprToBDDTransformer::sortVec(std::vector<BDDInterval> &vec)
{
    sortVec(vec, [&](auto &a, auto &b) { return bddManager.nodeCount(std::vector<BDD>{ a.upper }) < bddManager.nodeCount(std::vector<BDD>{ b.upper }); });
}

void ExprToBDDTransformer::sortVec(std::vector<std::pair<z3::expr, unsigned int>> &vec)
{
    sortVec(vec, [](auto &a, auto &b) { return a.second < b.second; });
}

//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////// PUBLIC FUNCTIONS //////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

void ExprToBDDTransformer::PrintNecessaryValues(BDD bdd)
{
    for (const auto &c : constSet) {
        PrintNecessaryVarValues(bdd, c.first);
    }
}

Model ExprToBDDTransformer::GetModel(BDD modelBdd)
{
    Model model;
    std::vector<BDD> modelVars;

    for (const auto &[name, bw] : constSet) {
        auto varBvec = vars.at(name);
        for (int i = bw - 1; i >= 0; i--) {
            if (varBvec[i].IsVar()) {
                modelVars.push_back(varBvec[i].GetBDD(bddManager.bddZero()));
            };
        }
    }

    modelBdd = modelBdd.PickOneMinterm(modelVars);

    for (const auto &[name, bw] : constSet) {
        vector<bool> modelBV(bw);

        const auto &[varBvec, _opPrecise, _varPrecise] = getApproximatedVariable(name, variableBitWidth, approximationType);
        for (int i = 0; i < bw; i++) {
            if ((modelBdd & !varBvec[i].GetBDD(bddManager.bddZero())).IsZero()) {
                modelBV[bw - i - 1] = true;
                modelBdd &= varBvec[i].GetBDD(bddManager.bddZero());
            } else {
                modelBV[bw - i - 1] = false;
                modelBdd &= !varBvec[i].GetBDD(bddManager.bddZero());
            }
        }

        const auto varSort = varSorts.find(name)->second;
        if (varSort.is_bool()) {
            model.insert({ name, modelBV[0] });
        } else {
            model.insert({ name, modelBV });
        }
    }

    return model;
}

void ExprToBDDTransformer::PrintModel(const map<string, vector<bool>> &model)
{
    std::cout << "Model: " << std::endl;
    std::cout << "---" << std::endl;

    for (auto &varModel : model) {
        std::cout << "  " << varModel.first << " = #b";
        for (auto bit : varModel.second) {
            std::cout << bit;
        }
        std::cout << ";" << std::endl;
    }

    std::cout << "---" << std::endl;
}

void ExprToBDDTransformer::PrintNecessaryVarValues(BDD bdd, const std::string &varName)
{
    if (!config.propagateNecessaryBits || variableBitWidth > 2) {
        return;
    }

    bdd = bdd.FindEssential();

    auto &bvec = vars.at(varName);

    bool newVal = false;
    for (unsigned i = 0; i < bvec.bitnum(); i++) {
        if ((bdd & !bvec[i].GetBDD(bddManager.bddZero())).IsZero()) {
            bvec[i] = MaybeBDD{ bddManager.bddOne() };
            newVal = true;
        } else if ((bdd & bvec[i].GetBDD(bddManager.bddZero())).IsZero()) {
            bvec[i] = MaybeBDD{ bddManager.bddZero() };
            newVal = true;
        } else if (i != bvec.bitnum() - 1 && (bdd & (bvec[bvec.bitnum() - 1].GetBDD(bddManager.bddZero()) ^ bvec[i].GetBDD(bddManager.bddZero()))).IsZero()) {
            bvec[i] = bvec[bvec.bitnum() - 1];
            newVal = true;
        }
    }

    if (newVal) {
        caches.clearCurrentBwAndPrecCaches();
    }
}

template <typename Top, typename TisDefinite, typename TdefaultResult>
    BDDInterval ExprToBDDTransformer::getConnectiveBdd(const std::vector<z3::expr> &arguments, const std::vector<boundVar> &boundVars, bool onlyExistentials, bool isPositive, Top &&op, TisDefinite &&isDefinite, TdefaultResult &&defaultResult)
    {
        
        std::vector<BDDInterval> bddSubResults;

        for (unsigned int i = 0; i < arguments.size(); i++) {
            if (isInterrupted()) {
                std::cout << "interrupted" << std::endl;
                return defaultResult;
            }
            //std::cout << "Argument i = " << i << " expr : " << arguments[i].to_string() << std::endl;
            bddSubResults.push_back(getBDDFromExpr(arguments[i], boundVars, onlyExistentials, isPositive));

            if (!bddSubResults.empty() && isDefinite(bddSubResults.back())) {
                return bddSubResults.back();
            }
        }

        if (bddSubResults.empty()) {
            return defaultResult;
        }

        if (!config.lazyEvaluation ) {
            sortVec(bddSubResults);
        }

        auto toReturn = defaultResult;
        for (auto &argBdd : bddSubResults) {
            if (isInterrupted()) {
                return defaultResult;
            }
            toReturn = op(toReturn, argBdd);
            if (isDefinite(toReturn)) {
                return toReturn;
            }
        }

        return toReturn;
    }