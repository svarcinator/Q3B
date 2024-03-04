#ifndef ExprToBDDTransformer_h
#define ExprToBDDTransformer_h

#include <string>
#include <set>
#include <vector>
#include <map>
#include <functional>
#include <unordered_map>
#include <iostream>
#include <algorithm> 

#include "cudd.h"
#include <cuddObj.hh>
#include "cudd/bvec_cudd.h"
#include <z3++.h>



#include "Model.h"
#include "Caches.h"
#include "VariableOrderer.h"
#include "Approximated.h"
#include "Config.h"
#include "BDDInterval.h"
#include "BWChangeEffect.h"

typedef std::pair<std::string, int> var;
enum IncrementedApproxStyle {BIT_WIDTH, PRECISION};

typedef std::pair<std::string, BoundType> boundVar;

using namespace cudd;

class ExprToBDDTransformer
{
  private:
    Cudd bddManager;

    std::map<std::string, Bvec> vars;
    std::map<std::string, BDD> varSets;
    std::map<std::string, std::vector<int>> varIndices;
    std::map<std::string, z3::sort> varSorts;

    std::set<var> constSet;
    std::set<var> boundVarSet;

    Caches caches;

    int lastBW = 0;

    std::set<Z3_ast> processedVarsCache;

    z3::context *context;

    void getVars(const z3::expr &e);
    void loadVars();

    BDDInterval loadBDDsFromExpr(z3::expr);
    BDDInterval getBDDFromExpr(const z3::expr &, const std::vector<boundVar> &, bool onlyExistentials, bool isPositive);
    Approximated<Bvec> getApproximatedVariable(const std::string &, int, const ApproximationType &);
    Approximated<Bvec> getBvecFromExpr(const z3::expr &, const std::vector<boundVar> &);

    
    uint posToEvaluate(const z3::expr &, const z3::expr &);
    BDDInterval getImplSubBDD(const uint, const z3::expr &, const std::vector<boundVar> &, bool onlyExistentials, bool isPositive);

    template <typename T, typename TorderFunc>
    void sortVec(std::vector<T> &vec, TorderFunc &&orderExpr);

    void sortVec(std::vector<BDDInterval> &vec);

    void sortVec(std::vector<std::pair<z3::expr, unsigned int>> &vec);

    template <typename Top, typename TisDefinite, typename TdefaultResult>
    BDDInterval getConnectiveBdd(const std::vector<z3::expr> &arguments, const std::vector<boundVar> &boundVars, bool onlyExistentials, bool isPositive, Top &&op, TisDefinite &&isDefinite, TdefaultResult &&defaultResult);


    

    BDDInterval getConjunctionBdd(const std::vector<z3::expr> &, const std::vector<boundVar> &, bool, bool);
    BDDInterval getDisjunctionBdd(const std::vector<z3::expr> &, const std::vector<boundVar> &, bool, bool);


    // Get Bvecs functions
    // Functions called in ExprToBDDTransformer::getBvecFromExpr 
    Approximated<Bvec> getVar(const z3::expr &e, const std::vector<boundVar> &);
    Approximated<Bvec> getConst(const z3::expr &e, const std::vector<boundVar> &);
    Approximated<Bvec> getShiftLeft(const z3::expr &e, const std::vector<boundVar> &);
    Approximated<Bvec> getShiftRight(const z3::expr &e, const std::vector<boundVar> &);
    Approximated<Bvec> getBNot(const z3::expr &e, const std::vector<boundVar> &);
    Approximated<Bvec> getBNeg(const z3::expr &e, const std::vector<boundVar> &);
    Approximated<Bvec> getBOr(const z3::expr &e, const std::vector<boundVar> &);
    Approximated<Bvec> getBAnd(const z3::expr &e, const std::vector<boundVar> &);
    Approximated<Bvec> getBXor(const z3::expr &e, const std::vector<boundVar> &);
    Approximated<Bvec> getAddition(const z3::expr &e, const std::vector<boundVar> &);
    Approximated<Bvec> getSubstraction(const z3::expr &e, const std::vector<boundVar> &);
    Approximated<Bvec> getConcat(const z3::expr &e, const std::vector<boundVar> &);
    Approximated<Bvec> getExtract(const z3::expr &e, const std::vector<boundVar> &);
    Approximated<Bvec> getMul(const z3::expr &e, const std::vector<boundVar> &);
    Approximated<Bvec> getDivOrRem(const z3::expr &e, const std::vector<boundVar> &);
    Approximated<Bvec> getSignedDivRem(const z3::expr &e, const std::vector<boundVar> &boundVars, z3::expr (*op)( const z3::expr &e1, const z3::expr &e2));
    Approximated<Bvec> getIte(const z3::expr &e, const std::vector<boundVar> &);

    Approximated<Bvec> getConcatApproximated(const z3::expr &e, const std::vector<boundVar> &boundVars, const Approximated<Bvec>&);

    // helper funcs
    void checkEqual(const Approximated<Bvec>& approxRes, const Approximated<Bvec>& orig);
    void checkEqual(const Approximated<Bvec>& approxRes, const std::function<Approximated<Bvec>()> &op);
    Approximated<Bvec> shiftNumeral(const z3::expr &e, const std::vector<boundVar> &, int );
    Bvec computeConcat(const z3::expr &e, Bvec , Bvec , int , int , bool , std::vector<Interval>&  );
    Approximated<Bvec> getExtractBvec(const z3::expr &e, const std::vector<boundVar> &boundVars, int bitFrom,int extractBits ) ;
    Approximated<Bvec> getCurrentBvec(const z3::expr &e, const std::vector<boundVar> &boundVars, int, bool& )  ;
    Bvec bvec_mul(Bvec &, Bvec &, Computation_state &);
    bool ApproximateOps() const;
    bool ApproximateVars() const;
    bool shouldApproximateVar(const boundVar& bVar) const;
    unsigned int getNumeralValue(const z3::expr &) const;
    Bvec getNumeralBvec(const z3::expr &);
    bool isMinusOne(const Bvec &);

    std::vector<boundVar> getNewBounds(const z3::expr &e, const std::vector<boundVar> &boundVars);

    Approximation approximation;
    ApproximationType approximationType;
    IncrementedApproxStyle incrementedApproxStyle;  // what change most recently -- bitwidth or precision
    int variableBitWidth;
    unsigned int operationPrecision;

    

    //bool variableApproximationHappened = false;
    bool operationApproximationHappened = false;

    int cacheHits = 0;

    BDDInterval bvec_ule(Bvec &, Bvec &, bool);
    BDDInterval bvec_ult(Bvec &, Bvec &, bool);
    Approximated<Bvec> bvec_assocOp(const z3::expr &, const std::function<Bvec(Bvec, Bvec)> &, const std::vector<boundVar> &);
    Approximated<Bvec> bvec_binOp(const z3::expr &, const std::function<Bvec(Bvec, Bvec)> &, const std::vector<boundVar> &);
    Approximated<Bvec> bvec_unOp(const z3::expr &, const std::function<Bvec(Bvec)> &, const std::vector<boundVar> &);


    Approximated<Bvec> bvec_binaryOpApprox(const z3::expr &e, const std::function<Bvec(Bvec, Bvec, std::vector<Interval>)> &op, 
                                            const std::function<std::vector<Interval>(std::vector<Interval>,std::vector<Interval>)>& intervalOp,
                                            const std::vector<boundVar> &);
    Approximated<Bvec> 
    bvec_unOpApprox(const z3::expr &e, const std::function<Bvec(Bvec, std::vector<Interval>)> &op,
                                                            const std::function<std::vector<Interval>(std::vector<Interval>)>& intervalOp, 
                                                            const std::vector<boundVar> &boundVars);

    Approximated<Bvec> 
    bvec_assocOpApprox(const z3::expr &e, const std::function<Bvec(Bvec, Bvec, std::vector<Interval>)> &op, 
                                                                const std::function<std::vector<Interval>(std::vector<Interval>,std::vector<Interval>)>& intervalOp,
                                                                const std::vector<boundVar> &boundVars);
    Config config;

    template <int n>
    void checkNumberOfArguments(const z3::expr &e)
    {
        if (e.num_args() != n) {
            std::cout << e << " -- unsupported number of arguments" << std::endl;
            std::cout << "unknown" << std::endl;
            exit(1);
        }
    }

    bool isInterrupted();

  public:
    ExprToBDDTransformer(z3::context &context, z3::expr e, Config config);

    z3::expr expression;
    BDD Proccess();

    BDDInterval ProcessUnderapproximation(int, unsigned int);
    BDDInterval ProcessOverapproximation(int, unsigned int);

    void setApproximationType(ApproximationType at)
    {
        approximationType = at;
    }
    /*
    bool IsPreciseResult()
    {
        return !variableApproximationHappened && !operationApproximationHappened;
    }

    bool VariableApproximationHappened()
    {
        return variableApproximationHappened;
    }
    */
    bool OperationApproximationHappened()
    {
        return operationApproximationHappened;
    }
    

    void configureReorder()
    {
        if (config.reorderType != NO_REORDER) {
            switch (config.reorderType) {
            case WIN2:
                bddManager.AutodynEnable(CUDD_REORDER_WINDOW2);
                break;
            case WIN2_ITE:
                bddManager.AutodynEnable(CUDD_REORDER_WINDOW2_CONV);
                break;
            case WIN3:
                bddManager.AutodynEnable(CUDD_REORDER_WINDOW3);
                break;
            case WIN3_ITE:
                bddManager.AutodynEnable(CUDD_REORDER_WINDOW3_CONV);
                break;
            case SIFT:
                bddManager.SetMaxGrowth(1.05);
                bddManager.SetSiftMaxVar(1);
                bddManager.AutodynEnable(CUDD_REORDER_SYMM_SIFT);
                break;
            case SIFT_ITE:
                bddManager.SetMaxGrowth(1.05);
                bddManager.SetSiftMaxVar(1);
                bddManager.AutodynEnable(CUDD_REORDER_SYMM_SIFT_CONV);
                break;
            default:
                break;
            }
        }
    }

    void PrintModel(const std::map<std::string, std::vector<bool>> &);
    Model GetModel(BDD);

    void PrintNecessaryValues(BDD);
    void PrintNecessaryVarValues(BDD, const std::string &);
};

#endif
