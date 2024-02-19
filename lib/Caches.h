#ifndef Caches_h
#define Caches_h


#include <vector>
#include <map>
#include <z3++.h>
#include "Approximated.h"
#include "cudd.h"
#include <cuddObj.hh>
#include "cudd/bvec_cudd.h"
#include "BDDInterval.h"


enum BoundType { EXISTENTIAL, UNIVERSAL };
enum ApproximationType { ZERO_EXTEND, SIGN_EXTEND };
enum Approximation { UNDERAPPROXIMATION, OVERAPPROXIMATION, NO_APPROXIMATION };

typedef std::pair<std::string, BoundType> boundVar;
using namespace cudd;

class Caches 
{
    public:

    std::map<std::pair<const Z3_ast, bool>, std::pair<BDDInterval, std::vector<boundVar>>> preciseBdds;
    std::map<const Z3_ast, std::pair<Approximated<Bvec>, std::vector<boundVar>>> preciseBvecs;
    // Sofar not used anywhere

    std::map<std::pair<const Z3_ast, bool>, std::pair<BDDInterval, std::vector<boundVar>>> bddExprCache;
    std::map<const Z3_ast, std::pair<Approximated<Bvec>, std::vector<boundVar>>> bvecExprCache;

    std::map<std::pair<const Z3_ast, bool>, std::pair<BDDInterval, std::vector<boundVar>>> sameBWPreciseBdds;
    std::map<const Z3_ast, std::pair<Approximated<Bvec>, std::vector<boundVar>>> sameBWPreciseBvecs;

    std::map<const Z3_ast, std::pair<Computation_state , std::vector<boundVar>>> sameBWImpreciseBvecStates;

    Approximated<Bvec> insertIntoCaches(const z3::expr&, const Approximated<Bvec>&, const std::vector<boundVar>&);
    BDDInterval insertIntoCaches(const z3::expr&, const BDDInterval&, const std::vector<boundVar>&, bool);
    void insertStateIntoCaches(const z3::expr &expr, const Computation_state& , const std::vector<boundVar> &,  const Approximated<Bvec>&, const bool);
    void clearCaches();
    void clearCurrentBwAndPrecCaches();
    void clearCurrentBwCaches();
    bool correctBoundVars(const std::vector<boundVar> &boundVars, const std::vector<boundVar> &cachedBoundVars) const;
    std::optional<Approximated<cudd::Bvec>> foundExprInCaches(const z3::expr &e,const std::vector<boundVar> &boundVars) const;
    std::optional<BDDInterval> foundExprInCaches(const z3::expr &e,const std::vector<boundVar> &, bool ) const;
    Computation_state findStateInCaches(const z3::expr &e,const std::vector<boundVar> &) const;

    void pruneBvecCache(const std::vector<boundVar>& );
    void pruneBddCache(const std::vector<boundVar>& );
};
#endif