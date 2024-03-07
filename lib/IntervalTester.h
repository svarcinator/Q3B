#pragma once
#include <vector>
#include <utility>

typedef std::pair<int, int> Interval;

class IntervalTester {

public:

    static bool 
    testNotNegative(const Interval &interval);

    static bool 
    testNotNegative(const std::vector<Interval> &intervals);

    static bool 
    testIntervalPair(const Interval &interval);

    static bool 
    testIntervalsOverlap(const std::vector<Interval> &intervals);

    static bool 
    testIntervalsOrder(const std::vector<Interval> &intervals);

    static bool 
    testIntervals(const std::vector<Interval>& vec);

    
};