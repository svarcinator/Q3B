#include "Caches.h"

#include "IntervalTester.h"

#define DEBUG false

Approximated<Bvec> Caches::insertIntoCaches(const z3::expr &expr, const Approximated<Bvec> &bvec, const std::vector<boundVar> &boundVars)
{
    bvecExprCache.insert({ (Z3_ast) expr, { bvec, boundVars } });

    if (bvec.value.isPrecise()) { //isPresise iff does not contain ? value
        sameBWPreciseBvecs.insert({ (Z3_ast) expr, { bvec, boundVars } });
    }
    return bvec;
}
BDDInterval Caches::insertIntoCaches(const z3::expr &expr, const BDDInterval &bdd, const std::vector<boundVar> &boundVars, bool isPositive)
{
    bddExprCache.insert({ { (Z3_ast) expr, isPositive }, { bdd, boundVars } });

    if (bdd.upper == bdd.lower) {
        sameBWPreciseBdds.insert({ { (Z3_ast) expr, isPositive }, { bdd, boundVars } });
    }

    return bdd;
}

void Caches::insertStateIntoCaches(const z3::expr &expr, const Computation_state &state, const std::vector<boundVar> &boundVars, const Approximated<Bvec> &bvec, const bool newState)
{
    //std::cout << "insertStateIntoCaches " << expr.to_string() << " state: " << state.to_string() << "  already in map? " << expr_already_in_map << std::endl;;
    if (!bvec.value.isPrecise() && !state.bitvec.empty() && bvec.value.bddNodes() != 0) {
        if (!newState) {
            sameBWImpreciseBvecStates[expr] = { state, boundVars };
            return;
        }
        sameBWImpreciseBvecStates.insert({ (Z3_ast) expr, { state, boundVars } });
        //std::cout << "Expr " << expr.to_string() << " inserted" << std::endl;
    }
    // if precise and in sameBWImpreciseBvecStates -> remove
    if (!newState && bvec.value.isPrecise()) {
        sameBWImpreciseBvecStates.erase(expr);
    }
}

void Caches::insertInterval(const z3::expr &e, const std::vector<Interval> &interval)
{
    if (DEBUG) {
        IntervalTester::testIntervals(interval);
    }

    intervals.insert({ (Z3_ast) e, interval });
}

void Caches::clearCaches()
{
    bddExprCache.clear();
    bvecExprCache.clear();
    //preciseBdds.clear(); // never to be cleared since they are precise
    //preciseBvecs.clear();
    sameBWPreciseBdds.clear();
    sameBWPreciseBvecs.clear();
    sameBWImpreciseBvecStates.clear();
    prevBWpreciseBvecs.clear();
    intervals.clear();
}
// clears caches that store objest for current bitwidth and precision
void Caches::clearCurrentBwAndPrecCaches()
{
    bddExprCache.clear();
    bvecExprCache.clear();
}

// clears caches that store objest for current bitwidth
// if only precision changes, do not clear
void Caches::clearCurrentBwCaches()
{
    sameBWPreciseBdds.clear();
    sameBWPreciseBvecs.clear();
    sameBWImpreciseBvecStates.clear();
    intervals.clear();
}

bool Caches::correctBoundVars(const std::vector<boundVar> &boundVars, const std::vector<boundVar> &cachedBoundVars) const
{
    if (boundVars.size() > cachedBoundVars.size()) {
        return false;
    }

    int pairsCount = std::min(boundVars.size(), cachedBoundVars.size());

    for (int i = 0; i < pairsCount; i++) {
        if (cachedBoundVars[cachedBoundVars.size() - i - 1] != boundVars[boundVars.size() - i - 1]) {
            return false;
        }
    }

    return true;
}

void Caches::incrementCache(int cacheType)
{
    switch (cacheType) {
    

    case 0:
        ++cacheHits.sameBWPreciseBddsHits;
        break;

    case 1:
        ++cacheHits.bddExprCacheHits;
        break;

    case 2:
        ++cacheHits.prevBWpreciseBvecsHits;
        break;

    case 3:
        ++cacheHits.intervalsHits;
        break;
    
    case 4:
        ++cacheHits.sameBWPreciseBvecsHits;
        break;

    case 5:
        ++cacheHits.bvecExprCacheHits;
        break;

    case 6:
        ++cacheHits.sameBWImpreciseBvecStatesHits;
        break;

    default:
        assert(false);
    }
}
std::optional<Approximated<cudd::Bvec>> Caches::foundExprInCaches(const z3::expr &e, const std::vector<boundVar> &boundVars)
{
    auto caches = { sameBWPreciseBvecs, bvecExprCache  };
    int counter = 4;
    for (const auto &cache : caches) {
        auto item = cache.find((Z3_ast) e);
        if (item != cache.end() && correctBoundVars(boundVars, (item->second).second)) {
            incrementCache(counter);
            return (item->second).first;
        }
        ++counter;
    }
    return {};
}

std::optional<BDDInterval> Caches::foundExprInCaches(const z3::expr &e, const std::vector<boundVar> &boundVars, bool isPositive)
{
    auto caches = { sameBWPreciseBdds, bddExprCache  };
    int counter = 0;
    for (const auto &cache : caches) {
        auto item = cache.find({ (Z3_ast) e, isPositive });
        if (item != cache.end()) {
            if (correctBoundVars(boundVars, (item->second).second)) {
                incrementCache(counter);
                return (item->second).first;
            }
        }
        ++counter;
    }
    return {};
}

Computation_state Caches::findStateInCaches(const z3::expr &e, const std::vector<boundVar> &boundVars)
{
    auto item = sameBWImpreciseBvecStates.find((Z3_ast) e);
    if (item != sameBWImpreciseBvecStates.end() && correctBoundVars(boundVars, (item->second).second)) {
        ++cacheHits.sameBWImpreciseBvecStatesHits;
        return sameBWImpreciseBvecStates.at((Z3_ast) e).first;
    }
    return Computation_state();
}

std::optional<Approximated<cudd::Bvec>> Caches::findPrevBWPreciseBvec(const z3::expr &e, const std::vector<boundVar> &boundVars) 
{
    auto item = prevBWpreciseBvecs.find((Z3_ast) e);
    if (item != prevBWpreciseBvecs.end() && correctBoundVars(boundVars, (item->second).second)) {
        ++cacheHits.prevBWpreciseBvecsHits;
        return prevBWpreciseBvecs.at((Z3_ast) e).first;
    }
    return {};
}

Computation_state Caches::getstateFromBvec(const std::optional<Approximated<cudd::Bvec>> &bvec)
{
    if (bvec.has_value()) {
        return Computation_state(bvec.value().value.m_bitvec);
    }
    return Computation_state();
}

std::vector<Interval> Caches::findInterval(const z3::expr &e)
{
    auto item = intervals.find((Z3_ast) e);
    if (item != intervals.end()) {
        ++cacheHits.intervalsHits;
        return intervals.at((Z3_ast) e);
    }
    return { { INT_MAX, 0 } }; // if expr not found return maximal interval -> whole bvec will be recomputed
}

void Caches::pruneBvecCache(const std::vector<boundVar> &newBoundVars)
{
    for (auto it = bvecExprCache.begin(); it != bvecExprCache.end();) {
        if ((it->second).second == newBoundVars) {
            it = bvecExprCache.erase(it);
        } else {
            it++;
        }
    }
}

void Caches::pruneBddCache(const std::vector<boundVar> &newBoundVars)
{
    for (auto it = bddExprCache.begin(); it != bddExprCache.end();) {
        if ((it->second).second == newBoundVars) {
            it = bddExprCache.erase(it);
        } else {
            it++;
        }
    }
}

void Caches::resetCacheHits()
{
    cacheHits = CacheHits();
}

void Caches::setCurrentBWasPrevBW(const IntervalRecomputationType type, z3::context &context)
{
    if (type == ALL_OPS) {
        prevBWpreciseBvecs = sameBWPreciseBvecs;
    } else if (type == NO_OPS) {
        prevBWpreciseBvecs.clear();
    } else {
        prevBWpreciseBvecs.clear();
        // only demanding operations stay in cache -- sofar +, -
        std::set<Z3_decl_kind> declKinds = { Z3_OP_BADD, Z3_OP_BSUB };
        for (auto [key, val] : sameBWPreciseBvecs) {
            // tbd
            std::cout << "expr = " << Z3_get_ast_kind(context, key) << std::endl;
            if (Z3_get_ast_kind(context, key) == 1000)
                continue;
            auto e = z3::to_expr(context, key);
            if (e.is_var() || e.is_const()) {
                // prevBWpreciseBvecs.insert({key, val});
            } else if (e.is_app()) {
                z3::func_decl f = e.decl();
                auto decl_kind = f.decl_kind();
                if (declKinds.find(decl_kind) != declKinds.end()) {
                    prevBWpreciseBvecs.insert({ key, val });
                }
            }
        }
    }
}
