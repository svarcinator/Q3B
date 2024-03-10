#pragma once
#include <climits>
#include <sstream>

typedef std::pair<int, int> Interval;

struct Computation_state
{
    std::vector<Interval> intervals;
    unsigned int m = 0;  //multiplication
    //unsigned int i = 0u; // multiplication, division
    unsigned int preciseBdds = 0;
    std::vector<MaybeBDD> bitvec;    // multiplication, division (res)
    std::vector<MaybeBDD> remainder; // division
    std::vector<MaybeBDD> div;       // division

    Computation_state()
    {
        intervals = {{INT_MAX,0}};
        bitvec = std::vector<MaybeBDD>();
        remainder = std::vector<MaybeBDD>();
        div = std::vector<MaybeBDD>();
    }

    Computation_state(std::vector<Interval> interv)
    {
        intervals = interv;
        bitvec = std::vector<MaybeBDD>();
        remainder = std::vector<MaybeBDD>();
        div = std::vector<MaybeBDD>();
    }
    Computation_state(Interval interval)
    {
        intervals = {interval};
        bitvec = std::vector<MaybeBDD>();
        remainder = std::vector<MaybeBDD>();
        div = std::vector<MaybeBDD>();
    }
    Computation_state(std::vector<MaybeBDD> m_bitvec)
    {
        intervals = {{INT_MAX,0}};
        bitvec = m_bitvec;
        remainder = std::vector<MaybeBDD>();
        div = std::vector<MaybeBDD>();
    }

    std::string toString() const
    {
        std::stringstream ss;
        ss << "Computation state\n m: " << m << "\n";
        for (size_t i = 0 ; i < intervals.size(); ++i) {
            ss << "interval " << i << " is from " << intervals[i].first << " to " <<  intervals[i].second << "\n";
        }
        ss << " PreciseBdds: " << preciseBdds << "\n Size: " << bitvec.size() << std::endl;
        for (size_t i = 0; i < bitvec.size(); ++i) {
            ss << " Pos=" << i << ", value/nodes=" << bitvec[i].HasValue() << "/" << bitvec[i].NodeCount() <<  std::endl;
            if (bitvec[i].HasValue()){
                //bitvec[i].GetBDD().print(2,3);
            }
            
        }
        return ss.str();
    }

    bool IsFresh() const
    {
        return  (m ==0  && preciseBdds == 0 && bitvec.empty() && remainder.empty() && div.empty());
    }
    
};