#ifndef Caches_h
#define Caches_h

#include <vector>
#include <map>
#include <z3++.h>
#include <nlohmann/json.hpp>

#include "Approximated.h"
#include "cudd.h"
#include <cuddObj.hh>
#include "cudd/bvec_cudd.h"
#include "BDDInterval.h"
#include "Config.h"


enum BoundType
{
    EXISTENTIAL,
    UNIVERSAL
};
enum ApproximationType
{
    ZERO_EXTEND,
    SIGN_EXTEND
};
enum Approximation
{
    UNDERAPPROXIMATION,
    OVERAPPROXIMATION,
    NO_APPROXIMATION
};

typedef std::pair<std::string, BoundType> boundVar;
using namespace cudd;

class Caches
{
  public:
    int variableBitWidth;
    struct CacheHits
    {
        int preciseBddsHits = 0;
        int sameBWPreciseBddsHits = 0;
        int preciseBvecsHits = 0;
        int prevBWpreciseBvecsHits = 0;
        int intervalsHits = 0;
        int bddExprCacheHits = 0;
        int bvecExprCacheHits = 0;
        int sameBWPreciseBvecsHits = 0;
        int sameBWImpreciseBvecStatesHits = 0;
    };

    CacheHits cacheHits;
    void incrementCache(int cacheType);

    std::map<std::pair<const Z3_ast, bool>, std::pair<BDDInterval, std::vector<boundVar>>> preciseBdds;
    std::map<const Z3_ast, std::pair<Approximated<Bvec>, std::vector<boundVar>>> preciseBvecs;
    // Sofar not used anywhere

    std::map<const Z3_ast, std::pair<Approximated<Bvec>, std::vector<boundVar>>> prevBWpreciseBvecs;
    std::map<const Z3_ast, std::vector<Interval>> intervals;

    std::map<std::pair<const Z3_ast, bool>, std::pair<BDDInterval, std::vector<boundVar>>> bddExprCache;
    std::map<const Z3_ast, std::pair<Approximated<Bvec>, std::vector<boundVar>>> bvecExprCache;

    std::map<std::pair<const Z3_ast, bool>, std::pair<BDDInterval, std::vector<boundVar>>> sameBWPreciseBdds;
    std::map<const Z3_ast, std::pair<Approximated<Bvec>, std::vector<boundVar>>> sameBWPreciseBvecs;

    std::map<const Z3_ast, std::pair<Computation_state, std::vector<boundVar>>> sameBWImpreciseBvecStates;

    Approximated<Bvec> insertIntoCaches(const z3::expr &, const Approximated<Bvec> &, const std::vector<boundVar> &);
    BDDInterval insertIntoCaches(const z3::expr &, const BDDInterval &, const std::vector<boundVar> &, bool);
    void insertStateIntoCaches(const z3::expr &expr, const Computation_state &, const std::vector<boundVar> &, const Approximated<Bvec> &, const bool);
    void insertInterval(const z3::expr &e, const std::vector<Interval> &);

    void clearCaches();
    void clearCurrentBwAndPrecCaches();
    void clearCurrentBwCaches();
    bool correctBoundVars(const std::vector<boundVar> &boundVars, const std::vector<boundVar> &cachedBoundVars) const;

    std::optional<Approximated<cudd::Bvec>> foundExprInCaches(const z3::expr &e, const std::vector<boundVar> &boundVars);
    std::optional<BDDInterval> foundExprInCaches(const z3::expr &e, const std::vector<boundVar> &, bool);
    Computation_state findStateInCaches(const z3::expr &e, const std::vector<boundVar> &);
    std::optional<Approximated<cudd::Bvec>> findPrevBWPreciseBvec(const z3::expr &e, const std::vector<boundVar> &);
    std::vector<Interval> findInterval(const z3::expr &e);

    static Computation_state
    getstateFromBvec(const std::optional<Approximated<cudd::Bvec>> &bvec);

    void pruneBvecCache(const std::vector<boundVar> &);
    void pruneBddCache(const std::vector<boundVar> &);

    void resetCacheHits();

    void setCurrentBWasPrevBW(const IntervalRecomputationType type, z3::context &context);

    std::string to_string()
    {
        std::stringstream ss;

        ss << "Precise bdds size = " << preciseBdds.size() << std::endl;
        ss << "Precise bvecs size = " << preciseBvecs.size() << std::endl;
        ss << "prevBWpreciseBvecs bvecs size = " << prevBWpreciseBvecs.size() << std::endl;
        ss << "sameBWPreciseBdds bvecs size = " << sameBWPreciseBdds.size() << std::endl;
        ss << "sameBWPreciseBvecs bvecs size = " << sameBWPreciseBvecs.size() << std::endl;
        ss << "sameBWImpreciseBvecStates bvecs size = " << sameBWImpreciseBvecStates.size() << std::endl;

        return ss.str();
    }

    std::stringstream cacheHitsToJson()
    {
        nlohmann::json j;
        j["bvecExprCacheHits"] = cacheHits.bvecExprCacheHits;
        j["preciseBvecsHits"] = cacheHits.preciseBvecsHits;
        j["sameBWPreciseBvecsHits"] = cacheHits.sameBWPreciseBvecsHits;
        j["prevBWpreciseBvecsHits"] = cacheHits.prevBWpreciseBvecsHits;
        j["intervalsHits"] = cacheHits.intervalsHits;
        j["bddExprCacheHits"] = cacheHits.bddExprCacheHits;
        j["sameBWPreciseBddsHits"] = cacheHits.sameBWPreciseBddsHits;
        j["sameBWImpreciseBvecStatesHits"] = cacheHits.sameBWImpreciseBvecStatesHits;
        // Add other cache hit counters as needed

        std::stringstream ss;
        ss << j;
        return ss;
    }
};
#endif