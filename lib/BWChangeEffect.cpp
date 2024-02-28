#include "BWChangeEffect.h"

#include "IntervalTester.cpp"
#include "Solver.h"

#include <iostream>
#include <mutex>

using namespace z3;




// only if aproximated
// oldBW  = newBW - 2;
std::vector<Interval> BWChangeEffect::EffectOnVar(int newBW, uint bitCount)
{
    if (newBW < 2) {
        return {{INT_MAX, 0}};
    }
    assert(newBW != 0 && newBW % 2 == 0);
    // seems like there is always only middle extension applied
    int left_index = bitCount - (newBW / 2); // bitcount - (newitWidth / 2) - 1 is the first index tht is set to 0
    int right_index = newBW - (newBW / 2) - 1;
    if (left_index < right_index ) {return {};} // nothing to be computed
    return { { left_index, left_index }, { right_index, right_index } };
}

// tests interval on the input on basic properties
void BWChangeEffect::AreIntervalsCorrect(const std::vector<Interval> &intervals) 
{
    IntervalTester::testIntervals(intervals);
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
BWChangeEffect::ShiftLeft(const std::vector<Interval>& intervals , unsigned int offset) {
    std::vector<Interval> intervals_copy = intervals;
    for (Interval& interval : intervals_copy) {
        interval.first += offset;
        interval.second = (interval.second == INT_MAX) ? interval.second : interval.second + offset;
    }
    return intervals_copy;
}

std::vector<Interval>
BWChangeEffect::EffectOnConcat(const std::vector<Interval>& current, const std::vector<Interval>& arg , unsigned int offset) {
    auto shiftedArg = ShiftLeft(arg, offset);
    return EffectOfUnion(current, shiftedArg); 
}

std::vector<Interval> BWChangeEffect::getSortedIntervals(const std::vector<Interval>  &leftChange, const std::vector<Interval>  &rightChange) {
    std::vector<Interval> sorted;
    size_t left= 0, right =0;
    while( left + right < leftChange.size() + rightChange.size()) {
        if (right >= rightChange.size() || (( leftChange[left].first > rightChange[right].first 
        || (leftChange[left].first == rightChange[right].first && leftChange[left].second >= rightChange[right].second) ) 
        && left < leftChange.size())) {
            sorted.push_back(leftChange[left]);
            ++left;
        } else {
            sorted.push_back(rightChange[right]);
            ++right;
        }
    }
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
    /*
    printIntervals(leftChange, "leftChange");
    printIntervals(rightChange, "rightChange");
    printIntervals(sorted, "sorted");
    printIntervals(merged, "merged");
    */
    return merged;
}



