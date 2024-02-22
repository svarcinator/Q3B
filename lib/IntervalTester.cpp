#ifndef IntervalTester_cpp
#define IntervalTester_cpp

#include <vector>
#include <utility>
#include <cassert>

typedef std::pair<int, int> Interval;
////////////////////////////////
///// TEST INTERVAL ////////////
////////////////////////////////

bool testIntervalPair(const Interval &interval)
{
    return interval.first >= interval.second;
}

// @pre: non empty intervals vector
bool testIntervalsOverlap(const std::vector<Interval> &intervals)
{
    assert(!intervals.empty());
    if (intervals.size() == 1)
        return true;

    for (int i = 1; i < intervals.size(); ++i) {
        auto left = intervals[i - 1];
        auto right = intervals[i];
        // lowest of left interval is greater that greatest of right interval
        if (left.second == right.first)
            return false;
    }
    return true;
}

// @pre: non empty intervals vector
bool testIntervalsOrder(const std::vector<Interval> &intervals)
{
    assert(!intervals.empty());
    if (intervals.size() == 1)
        return true;

    for (int i = 1; i < intervals.size(); ++i) {
        auto left = intervals[i - 1];
        auto right = intervals[i];
        // lowest of left interval is greater that greatest of right interval
        if (left.second < right.first)
            return false;
    }
    return true;
}

bool testIntervals(const std::vector<Interval>& vec) {
    bool res = true;
    // First test each separate interval
    for (auto i : vec) {
        res = testIntervalPair(i);
        assert(res);
    }

    // Right order
    res = testIntervalsOrder(vec);
    assert(res);

    // Now only way that they could overlap if there would be lowest left equal to greatest right
    res = testIntervalsOverlap(vec);
    assert(res);
    return res;
}

#endif