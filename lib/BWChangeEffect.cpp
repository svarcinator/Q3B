#include "BWChangeEffect.h"

#include "IntervalTester.cpp"
#include "Solver.h"

#include <iostream>
#include <mutex>

using namespace z3;





// only if aproximated
// oldBW  = newBW - 2;
std::vector<Interval> BWChangeEffect::EffectOnVar(int newBW, uint bitCount) const
{
    assert(newBW != 0 && newBW % 2 == 0);
    // seems like there is always only middle extension applied
    int left_index = bitCount - (newBW / 2); // bitcount - (newitWidth / 2) - 1 is the first index tht is set to 0
    int right_index = newBW - (newBW / 2) - 1;
    return { { left_index, left_index }, { right_index, right_index } };
}

// tests interval on the input on basic properties
void BWChangeEffect::AreIntervalsCorrect(const std::vector<Interval> &intervals) 
{
    testIntervals(intervals);
}

int BWChangeEffect::getRightmostBit(const Interval &leftChange, const Interval &rightChange) const {
    return std::min(leftChange.second, rightChange.second);
}

std::vector<Interval> BWChangeEffect::EffectOnAddition(const std::vector<Interval>  &leftChange, const std::vector<Interval>  &rightChange) const
{
    // Recompute everything (to left) from the rightmost changed bit.
    // Because of carry bit

    auto rightmostChangedBit = getRightmostBit(leftChange.back(), rightChange.back());
    return {{INTMAX_MAX,rightmostChangedBit }};    // unbounded interval on left -- means from right to the left end of bitvector
}


