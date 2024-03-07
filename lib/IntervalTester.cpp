#include "IntervalTester.h"

#include <iostream>
#include <cassert>
#include <climits>

////////////////////////////////
///// TEST INTERVAL ////////////
////////////////////////////////
bool IntervalTester::testNotNegative(const Interval &interval) {
    return interval.second >= 0 && interval.first >= 0;
}

bool IntervalTester::testNotNegative(const std::vector<Interval> &intervals) {
    for (const Interval& interval: intervals) {
        if (!testNotNegative(interval) ) {
            return false;
        }
    }
    return true;
}


bool IntervalTester::testIntervalPair(const Interval &interval)
{
    return interval.first >= interval.second;
}

// @pre: non empty intervals vector
bool IntervalTester::testIntervalsOverlap(const std::vector<Interval> &intervals)
{
    //assert(!intervals.empty());
    if (intervals.size() <= 1)
        return true;

    for (std::size_t i = 1; i < intervals.size(); ++i) {
        auto left = intervals[i - 1];
        auto right = intervals[i];
        // lowest of left interval is greater that greatest of right interval
        if (left.second == right.first)
            return false;
    }
    return true;
}

// @pre: non empty intervals vector
bool IntervalTester::testIntervalsOrder(const std::vector<Interval> &intervals)
{
    //assert(!intervals.empty());
    if (intervals.size() <= 1)
        return true;

    for (std::size_t i = 1; i < intervals.size(); ++i) {
        auto left = intervals[i - 1];
        auto right = intervals[i];
        // lowest of left interval is greater that greatest of right interval
        if (left.second < right.first)
            return false;
    }
    return true;
}


void printIntervals(const std::vector<Interval>  &interv, std::string name) {
    std::cout << "Interval " << name << "= ";
    std::cout << "[ ";
    for (auto i : interv) {
        std::cout << "< " << i.first << ", " << i.second << " >, ";
    }
    std::cout << "] " << std::endl;
}

bool IntervalTester::testIntervals(const std::vector<Interval>& vec) {
    bool res = true;
    // First test each separate interval
    for (auto i : vec) {
        res = testIntervalPair(i);
        assert(res);
    }

    // Onl positive indices in interval
    res = testNotNegative(vec);
    assert(res);

    // Right order
    res = testIntervalsOrder(vec);
    assert(res);

    // Now only way that they could overlap if there would be lowest left equal to greatest right
    res = testIntervalsOverlap(vec);
    assert(res);
    return res;
}


