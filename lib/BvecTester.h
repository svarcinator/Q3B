#pragma once


#include <vector>
#include <map>
#include <z3++.h>

#include "Approximated.h"
#include "cudd.h"
#include <cuddObj.hh>
#include "cudd/bvec_cudd.h"
#include "BDDInterval.h"
#include "ComputationState.h"

typedef std::pair<int, int> Interval;

class BvecTester {

public:

    static bool 
    testBvNeg(const cudd::Bvec& orig,const cudd::Bvec& negated );

    static bool 
    testAddOrSub(const Approximated<cudd::Bvec>& approxResult,const Approximated<cudd::Bvec>& orig, const Computation_state& approxResultState);

    static bool 
    testBvecEq(const Approximated<cudd::Bvec>& approxResult,const Approximated<cudd::Bvec>& orig );

    static bool
    testBvecSize(size_t size, const Approximated<cudd::Bvec>& approxResult) ;

};
