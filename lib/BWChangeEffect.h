#ifndef BWChangeEffect_h
#define BWChangeEffect_h

#include <vector>
#include <map>
#include <utility> // contains std::pair
#include <z3++.h>
 
#include "Caches.h"


typedef std::pair<size_t, size_t> Interval;
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
    EffectOnAddorSub(const std::vector<Interval>  &leftChange, const std::vector<Interval>  &rightChange);
    static std::vector<Interval>
    EffectOnKid(const std::vector<Interval>  &kidChange);

    static std::vector<Interval>
    EffectFromLeastSignChangedBit(const std::vector<Interval>  &);

    static std::vector<Interval>
    ShiftLeft(const std::vector<Interval>  & , unsigned int);

    static std::vector<Interval>
    EffectOnConcat(const std::vector<Interval>& current, const std::vector<Interval>& arg,  unsigned int offset );
    
    static std::vector<Interval>
    EffectOfUnion(const std::vector<Interval>  &leftChange, const std::vector<Interval>  &rightChange);
    static Interval 
    merge(const Interval& l, const Interval& r) ;
    static bool 
    doOverlap(const Interval& l, const Interval& r);
    static std::vector<Interval> 
    getSortedIntervals(const std::vector<Interval>  &leftChange, const std::vector<Interval>  &rightChange);

    static void
    printIntervals(const std::vector<Interval>  &interv, std::string name);
};
#endif

// asi si tu znova naimplementuju cely svuj novy expr walk, ale nejspise by to pak chtelo nejaky poradnejsi refactoring, tak aby to nebylo vsude porad dokola
// stalo by za to si rozmyslet, jestli by to pak neslo nejak genericteji uvnitr preprocessingu (protoze precejenom by to melo byt furt podobne
// a to ze aff bits budou posledni dva (tzn na indexu BW -1 a BW -2), z toho se pak ovlivni vys a vys)

// a potom bychom pro kazdy expr vytvorili fci, co by brala na vstup currentBW a vracela vector IndexIntervalů
// mozna to bude lepsi udelat v konstruktoru transformeru, jelikoz tam uz jsou vytvorene promenne a vime jak jsou kvantifikovane
// dunno
