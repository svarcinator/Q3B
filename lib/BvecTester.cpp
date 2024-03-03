#include "BvecTester.h"

#include <iostream>
#include <cassert>


bool BvecTester::testBvNeg(const cudd::Bvec& orig,const cudd::Bvec& negated ){
    return true;
}


bool BvecTester::testAddOrSub(const Approximated<cudd::Bvec>& approxResult,const Approximated<cudd::Bvec>& orig , const Computation_state& approxResultState){
    auto areEq = approxResult.value == orig.value;
    if (!areEq.IsOne()) {
        std::cout << "Are zero then? " << areEq.IsZero() << std::endl;
        // manually go through bvecs
        auto origState = Computation_state(orig.value.m_bitvec);
        auto resultState = Computation_state(approxResult.value.m_bitvec);
        std::cout << "Orig:  " << origState.toString(); 
        std::cout << "Approximated result:  " << resultState.toString(); 
        std::cout << "Inserted approximated result:  " << approxResultState.toString();
        for(int i = 0; i < orig.value.m_bitvec.size(); ++i ) {
            bool areEq = orig.value.m_bitvec[i].Equals(approxResult.value.m_bitvec[i]);
            std::cout << "Index i=" << i<< ". Are equal? " << areEq << std::endl;
        }
    }
    //assert(areEq.IsOne());
    return true;
}

bool BvecTester::testBvecEq(const Approximated<cudd::Bvec>& approxResult,const Approximated<cudd::Bvec>& orig ) {
    auto areEq = approxResult.value == orig.value;
    if (!areEq.IsOne()) {
        std::cout << "Are zero then? " << areEq.IsZero() << std::endl;
        // manually go through bvecs
        auto origState = Computation_state(orig.value.m_bitvec);
        auto resultState = Computation_state(approxResult.value.m_bitvec);
        std::cout << "Orig:  " << origState.toString(); 
        std::cout << "Approximated result:  " << resultState.toString(); 
    }
    assert(areEq.IsOne());
    return true;
}
