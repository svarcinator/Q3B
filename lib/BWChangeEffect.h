#ifndef BWChangeEffect_h
#define BWChangeEffect_h

#include <vector>
#include <map>
#include <utility> // contains std::pair
#include <z3++.h>
 
#include "Caches.h"


typedef std::pair<int, int> Interval;

class BWChangeEffect
{
  private:
    /* data */

    
  public:
    std::map<z3::expr, std::vector<Interval>> AffectedIndices;
    // function f: int -> std::vector<Interval>> -- for current BW return intervals of affected bits
    std::map< z3::expr, std::function<std::vector<Interval>>(int)> AffectedIndicesFunc;

    void ExprWalk(const z3::expr &e);
    void EffectOnVar(const z3::expr &e);
    
};
#endif

