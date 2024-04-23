#ifndef BVECMULTIPLIER_H
#define BVECMULTIPLIER_H



#include <cuddObj.hh>
#include "cudd/bvec_cudd.h"
#include "cudd.h"

#include <vector>
#include <algorithm>

#include <tuple>


class BvecMultiplier
{
    // Bvec multiplication functions
  public:
    static bool isMinusOne(const cudd::Bvec &bvec)
    {
        return std::all_of(bvec.m_bitvec.begin(), bvec.m_bitvec.end(), [](auto &bit) { return bit.IsOne(); });
    }

    static void handleNegativeOneSpecialCase(cudd::Bvec &a, cudd::Bvec &b)
    {
        if (isMinusOne(a)) {
            cudd::Bvec::arithmetic_neg(b);
        } else if (isMinusOne(b)) {
            cudd::Bvec::arithmetic_neg(a);
        }
    }

    static bool canUseOptimizedMultiplication(const cudd::Bvec &a, const cudd::Bvec &b)
    {
        return a.bitnum() <= 32 && b.bitnum() <= 32 && (a.bvec_isConst() || b.bvec_isConst());
    }

    static std::tuple<cudd::Bvec, bool> performOptimizedMultiplication(cudd::Bvec &a, cudd::Bvec &b)
    {
        if (b.bvec_isConst()) {
            std::swap<cudd::Bvec>(a, b);
        }
        if (a.bvec_isConst()) {
            unsigned int val = a.bvec_val();
            unsigned int shiftCount = countTrailingZeros(val);
            val >>= shiftCount;
            if (shiftCount > 0) {
                cudd::Bvec result = (b * val) << shiftCount;
                return { result, true };
            }

            if (val <= INT_MAX) {
                return { b * val, true };
            }
        }
        return { a, false };
    }

    static unsigned int countTrailingZeros(unsigned int val)
    {
        unsigned int count = 0;
        for (; val % 2 == 0 && count < 64; ++count) {
            val >>= 1;
        }
        return count;
    }

    static void optimizeBitHandling(cudd::Bvec &a, cudd::Bvec &b)
    {
        int leftConstantCount = countConstantBits(a);
        int rightConstantCount = countConstantBits(b);
        if (leftConstantCount < rightConstantCount) {
            std::swap<cudd::Bvec>(a, b);
        }
    }

    static int countConstantBits(const cudd::Bvec &vec) 
    {
        int count = 0;
        for (unsigned int i = 0; i < vec.bitnum(); i++) {
            if (vec[i].IsZero() || vec[i].IsOne()) {
                count++;
            }
        }
        return count;
    }

    static cudd::Bvec performApproximateMultiplication(cudd::Bvec &a, cudd::Bvec &b, Computation_state &state, unsigned int nodeLimit) {
    return  cudd::Bvec::bvec_mul_nodeLimit_state(a, b, nodeLimit, state).bvec_coerce(a.bitnum());
}
};
#endif