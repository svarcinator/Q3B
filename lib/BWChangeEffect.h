#ifndef BWChangeEffect_h
#define BWChangeEffect_h

#include <vector>
#include <map>
#include <utility> // contains std::pair
#include <z3++.h>
 
#include "Caches.h"


typedef std::pair<int, int> Interval;
typedef std::pair<std::string, int> var;


class BWChangeEffect
{
  private:
    
    
  public:

    static std::vector<Interval>
    EffectOnVar(int, uint);
    
    static void 
    AreIntervalsCorrect(const std::vector<Interval> &intervals);
   
    static int 
    getRightmostBit(const Interval &leftChange, const Interval &rightChange);
    static std::vector<Interval> 
    EffectOnAddition(const std::vector<Interval>  &leftChange, const std::vector<Interval>  &rightChange);

};
#endif

// asi si tu znova naimplementuju cely svuj novy expr walk, ale nejspise by to pak chtelo nejaky poradnejsi refactoring, tak aby to nebylo vsude porad dokola
// stalo by za to si rozmyslet, jestli by to pak neslo nejak genericteji uvnitr preprocessingu (protoze precejenom by to melo byt furt podobne
// a to ze aff bits budou posledni dva (tzn na indexu BW -1 a BW -2), z toho se pak ovlivni vys a vys)

// a potom bychom pro kazdy expr vytvorili fci, co by brala na vstup currentBW a vracela vector IndexIntervalů
// mozna to bude lepsi udelat v konstruktoru transformeru, jelikoz tam uz jsou vytvorene promenne a vime jak jsou kvantifikovane
// dunno
