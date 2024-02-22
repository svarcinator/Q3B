
#include "Caches.h"

Approximated<Bvec> Caches::insertIntoCaches(const z3::expr &expr, const Approximated<Bvec> &bvec, const std::vector<boundVar> &boundVars)
{
    bvecExprCache.insert({ (Z3_ast) expr, { bvec, boundVars } });

    if (bvec.value.isPrecise()) {
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

void Caches::insertInterval(const z3::expr& e, const std::vector<Interval>& interval) {
    intervals.insert({(Z3_ast) e,interval });
}

void Caches::clearCaches()
{
    bddExprCache.clear();
    bvecExprCache.clear();
    preciseBdds.clear();
    preciseBvecs.clear();
    sameBWPreciseBdds.clear();
    sameBWPreciseBvecs.clear();
    sameBWImpreciseBvecStates.clear();
    prevBWpreciseBvecs.clear();
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

std::optional<Approximated<cudd::Bvec>> Caches::foundExprInCaches(const z3::expr &e, const std::vector<boundVar> &boundVars) const
{
    auto caches = { bvecExprCache, preciseBvecs, sameBWPreciseBvecs };
    for (const auto &cache : caches) {
        auto item = cache.find((Z3_ast) e);
        if (item != cache.end() && correctBoundVars(boundVars, (item->second).second)) {
            return (item->second).first;
        }
    }
    return {};
}

std::optional<BDDInterval> Caches::foundExprInCaches(const z3::expr &e, const std::vector<boundVar> &boundVars, bool isPositive) const
{
    auto caches = { bddExprCache, preciseBdds, sameBWPreciseBdds };
    for (const auto &cache : caches) {
        auto item = cache.find({ (Z3_ast) e, isPositive });
        if (item != cache.end()) {
            if (correctBoundVars(boundVars, (item->second).second)) {
                return (item->second).first;
            }
        }
    }
    return {};
}

Computation_state Caches::findStateInCaches(const z3::expr &e, const std::vector<boundVar> &boundVars) const
{
    auto item = sameBWImpreciseBvecStates.find((Z3_ast) e);
    if (item != sameBWImpreciseBvecStates.end() && correctBoundVars(boundVars, (item->second).second)) {
        return sameBWImpreciseBvecStates.at((Z3_ast) e).first; 
    }
    return { 0, 0, 0, std::vector<MaybeBDD>(), std::vector<MaybeBDD>(), std::vector<MaybeBDD>() };                
}

std::optional<Approximated<cudd::Bvec>> Caches::findPrevBWPreciseBvec(const z3::expr &e,const std::vector<boundVar> & boundVars )const
{
    auto item = prevBWpreciseBvecs.find((Z3_ast) e);
    if (item != prevBWpreciseBvecs.end() && correctBoundVars(boundVars, (item->second).second)) {
        return prevBWpreciseBvecs.at((Z3_ast) e).first; 
    }
    return {};   

}

std::vector<Interval> Caches::findInterval(const z3::expr& e) const
{
    auto item = intervals.find((Z3_ast) e);
    if (item != intervals.end() ) {
        return intervals.at((Z3_ast) e); 
    }
    return {{INT_MAX, 0}};    // if expr not found return maximal interval -> whole bvec will be recomputed
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

void Caches::setCurrentBWasPrevBW() {
        prevBWpreciseBvecs = preciseBvecs;
}
