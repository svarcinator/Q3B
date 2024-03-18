#include "BWChangeEffect.h"

#include "IntervalTester.cpp"
#include "Solver.h"

#include <iostream>
#include <mutex>


#define DEBUG false

using namespace z3;




// only if aproximated
// oldBW  = newBW - 2;
std::vector<Interval> BWChangeEffect::EffectOnVar(int newBW, uint bitCount,unsigned int operationPrecision )
{
    if (newBW <= 2 || (operationPrecision == 2 && newBW == 128) ) {
        return {{bitCount -1, 0}};
    }
    
    assert(newBW != 0 && newBW % 2 == 0);
    // seems like there is always only middle extension applied
    int left_index = bitCount - (newBW / 2); // bitcount - (newitWidth / 2) - 1 is the first index tht is set to 0
    int right_index = newBW - (newBW / 2) - 1;
    if (left_index < right_index ) {return {};} // nothing to be computed
    // return { { bitCount, left_index }, { right_index, 0 } };
    return { { left_index, left_index }, { right_index, right_index } };
}

// tests interval on the input on basic properties
void BWChangeEffect::AreIntervalsCorrect(const std::vector<Interval> &intervals) 
{
    //IntervalTester::testIntervals(intervals);
}

int BWChangeEffect::getRightmostBit(const Interval &leftChange, const Interval &rightChange)  {
    
    return std::min(leftChange.second, rightChange.second);
}

std::vector<Interval> BWChangeEffect::EffectOnAddorSub(const std::vector<Interval>  &leftChange, const std::vector<Interval>  &rightChange)
{
    // Recompute everything (to left) from the rightmost changed bit.
    // Because of carry bit
    if (leftChange.empty() && rightChange.empty()){
        return {};
    } else if (leftChange.empty()) {
        return  {{INT_MAX, rightChange.back().second }}; 
    } else if (rightChange.empty()) {
        return  {{INT_MAX, leftChange.back().second }}; 
    }
    auto rightmostChangedBit = getRightmostBit(leftChange.back(), rightChange.back());
    return {{INT_MAX,rightmostChangedBit }};    // unbounded interval on left -- means from right to the left end of bitvector
}

std::vector<Interval>
BWChangeEffect::EffectOnKid(const std::vector<Interval>  &kidChange) {
    return kidChange;
}
std::vector<Interval>
BWChangeEffect::EffectFromLeastSignChangedBit(const std::vector<Interval>  &kidChange) {
    if(kidChange.empty()) {
        return kidChange;
    }
    return {{INT_MAX,kidChange.back().second }}; 
}


std::vector<Interval>
BWChangeEffect::ShiftLeft(const std::vector<Interval>& intervals ,  int offset) {
    std::vector<Interval> intervals_copy = intervals;
    for (Interval& interval : intervals_copy) {
        interval.first = (interval.first == INT_MAX) ? interval.first : interval.first + offset;;
        interval.second += offset;
    }
    return intervals_copy;
}
bool BWChangeEffect::checkRightBound(const Interval& interval) {
    return interval.first >= 0;
}
std::vector<Interval>
BWChangeEffect::ShiftRight(const std::vector<Interval>& intervals ,  int offset) {
    auto intervals_copy = std::vector<Interval>();
    for (Interval interval : intervals) {
        // shift right
        interval.first = (interval.first == INT_MAX) ? interval.first : interval.first - offset;
        interval.second = std::max(0, interval.second - offset );
        //check bounds
        if (checkRightBound(interval)) {
            intervals_copy.push_back(interval);
        }
    }
    return intervals_copy;
}

std::vector<Interval>
BWChangeEffect::EffectOnConcat(const std::vector<Interval>& current, const std::vector<Interval>& arg , unsigned int offset) {
    auto shiftedArg = ShiftLeft(arg, offset);
    return EffectOfUnion(current, shiftedArg); 
}
// @pre: leftChange, rightChange are sorted
std::vector<Interval> BWChangeEffect::getSortedIntervals(const std::vector<Interval>  &leftChange, const std::vector<Interval>  &rightChange) {
    std::vector<Interval> sorted = {};
    size_t left= 0, right =0;

    while( (left + right) < (leftChange.size() + rightChange.size())) {
        if (right >= rightChange.size() || (left < leftChange.size() && ( leftChange[left].first > rightChange[right].first 
        || (leftChange[left].first == rightChange[right].first && leftChange[left].second >= rightChange[right].second) ) )) {
            sorted.push_back(leftChange[left]);
            ++left;
        } else {
            sorted.push_back(rightChange[right]);
            ++right;
        }
    }
    assert(sorted.size() == leftChange.size() + rightChange.size());
    return sorted;
}

bool BWChangeEffect::doOverlap(const Interval& l, const Interval& r) {
    return (l.first >= r.second  && r.first >=l.second ) || (l.second <= r.first && r.second <= l.first);
}

Interval BWChangeEffect::merge(const Interval& l, const Interval& r) {
    return {std::max(l.first, r.first) , std::min(l.second, r.second)};
}
void BWChangeEffect::printIntervals(const std::vector<Interval>  &interv, std::string name) {
    std::cout << "Interval " << name << "= ";
    std::cout << "[ ";
    for (auto i : interv) {
        std::cout << "< " << i.first << ", " << i.second << " >, ";
    }
    std::cout << "] " << std::endl;
}

std::vector<Interval>
BWChangeEffect::EffectOfUnion(const std::vector<Interval>  &leftChange, const std::vector<Interval>  &rightChange) {
    if (leftChange.empty()) {
        return rightChange;
    } else if (rightChange.empty()) {
        return leftChange;
    }
    auto sorted = getSortedIntervals(leftChange, rightChange);
    std::vector<Interval> merged = { sorted[0]};
    size_t sorted_idx = 1;
    while(sorted_idx < sorted.size()) {
        if (doOverlap(sorted[sorted_idx], merged.back())) {
            merged.back() = merge(sorted[sorted_idx], merged.back());
        } else {
            merged.push_back(sorted[sorted_idx]);
        }
        sorted_idx++;
    }
    
    // printIntervals(leftChange, "leftChange");
    // printIntervals(rightChange, "rightChange");
    // printIntervals(sorted, "sorted");
    // printIntervals(merged, "merged");
    
    return merged;
}

bool BWChangeEffect::checkRightBound(const Interval& interval, unsigned int highest_bit_index) {
    return interval.first <= highest_bit_index;
}

std::vector<Interval>
BWChangeEffect::CropInterval(const std::vector<Interval>& intervals , unsigned int highest_bit_index) {
    auto intervals_copy = std::vector<Interval>();
    for (auto i : intervals) {
        if (i.second > highest_bit_index) {
            continue;
        }
        else if (i.first > highest_bit_index) {
            i.first = highest_bit_index;
        }
        intervals_copy.push_back(i);
    }
    return intervals_copy;
}

std::vector<Interval>
BWChangeEffect::EffectOnExtract(const std::vector<Interval>  &childChange, int rightshift, int extractBits) {
    auto shifted = ShiftRight(childChange, rightshift);
    auto cropped = CropInterval(shifted, extractBits - 1);
    return cropped;
}

// shift >= 0 -> shiftleft else shiftright
std::vector<Interval>
BWChangeEffect::EffectOfShift(const std::vector<Interval>  &childChange, int shift) {
    std::vector<Interval> shifted;
    if (shift >= 0) {
        shifted = ShiftLeft(childChange, shift);
    }
    shifted = ShiftRight(childChange, -shift);
    if (DEBUG) {
        AreIntervalsCorrect(shifted);
    }
    return shifted;
}





