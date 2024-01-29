#ifndef ExprToBDDTransformer_h
#define ExprToBDDTransformer_h

#include <string>
#include <set>
#include <vector>
#include <map>
#include <functional>
#include <unordered_map>
#include "cudd.h"
#include <cuddObj.hh>
#include "cudd/bvec_cudd.h"
#include <z3++.h>
#include "VariableOrderer.h"
#include "Approximated.h"
#include "Config.h"
#include "BDDInterval.h"
#include <iostream>
#include <algorithm> 

#include "Model.h"

typedef std::pair<std::string, int> var;

enum BoundType { EXISTENTIAL, UNIVERSAL };
enum ApproximationType { ZERO_EXTEND, SIGN_EXTEND };
enum Approximation { UNDERAPPROXIMATION, OVERAPPROXIMATION, NO_APPROXIMATION };

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

    std::map<std::pair<const Z3_ast, bool>, std::pair<BDDInterval, std::vector<boundVar>>> bddExprCache;
    std::map<const Z3_ast, std::pair<Approximated<Bvec>, std::vector<boundVar>>> bvecExprCache;

    // Where is this used? Where are used?
    std::map<std::pair<const Z3_ast, bool>, std::pair<BDDInterval, std::vector<boundVar>>> preciseBdds;
    std::map<const Z3_ast, std::pair<Approximated<Bvec>, std::vector<boundVar>>> preciseBvecs;

    int lastBW = 0;
    std::map<std::pair<const Z3_ast, bool>, std::pair<BDDInterval, std::vector<boundVar>>> sameBWPreciseBdds;
    std::map<const Z3_ast, std::pair<Approximated<Bvec>, std::vector<boundVar>>> sameBWPreciseBvecs;

    std::map<const Z3_ast, std::pair<Approximated<Bvec>, std::vector<boundVar>>> sameBWImpreciseBvecs;


    Approximated<Bvec> insertIntoCaches(const z3::expr&, const Approximated<Bvec>&, const std::vector<boundVar>&);
    BDDInterval insertIntoCaches(const z3::expr&, const BDDInterval&, const std::vector<boundVar>&, bool);

    std::set<Z3_ast> processedVarsCache;

    z3::context* context;

    void getVars(const z3::expr &e);
    void loadVars();

    BDDInterval loadBDDsFromExpr(z3::expr);
    bool correctBoundVars(const std::vector<boundVar>&, const std::vector<boundVar>&) const;
    BDDInterval getBDDFromExpr(const z3::expr&, const std::vector<boundVar>&, bool onlyExistentials, bool isPositive);
    Approximated<Bvec> getApproximatedVariable(const std::string&, int, const ApproximationType&);
    Approximated<Bvec> getBvecFromExpr(const z3::expr&, const std::vector<boundVar>&);

    unsigned int getNumeralValue(const z3::expr&) const;
    Bvec getNumeralBvec(const z3::expr&);
    bool isMinusOne(const Bvec&);
    uint posToEvaluate(const z3::expr&, const z3::expr&);
    BDDInterval getImplSubBDD(const uint, const z3::expr&,  const std::vector<boundVar>&, bool onlyExistentials, bool isPositive);

    template <typename T, typename TorderFunc>
    void sortVec(std::vector<T>& vec, TorderFunc&& orderExpr);

    void sortVec(std::vector<BDDInterval>& vec);

    void sortVec(std::vector<std::pair<z3::expr, unsigned int>>& vec);

    BDDInterval getBdd(unsigned int i, const std::vector<BDDInterval>& bddSubResults,
                        const std::vector<std::pair<z3::expr, unsigned int>>& exprExpensiveOpsVec,
                        const std::vector<boundVar>& boundVars, bool onlyExistentials, bool isPositive);


    template < typename Top,  typename TisDefinite, typename TdefaultResult >
    BDDInterval getConnectiveBdd(const std::vector<z3::expr>& arguments, const std::vector<boundVar>& boundVars, bool onlyExistentials, bool isPositive,
                                 Top&& op, TisDefinite&& isDefinite, TdefaultResult&& defaultResult)
    {
        std::vector<BDDInterval> bddSubResults;

        for (unsigned int i = 0; i < arguments.size(); i++)
        {
            if (isInterrupted()) { std::cout<< "interrupted" << std::endl; return defaultResult; }
            bddSubResults.push_back(getBDDFromExpr(arguments[i], boundVars, onlyExistentials, isPositive));

            if (!bddSubResults.empty() &&  isDefinite(bddSubResults.back())) { return bddSubResults.back();  }
        }
        
        if ( bddSubResults.empty()) { return defaultResult; }
       
        if (!config.lazyEvaluation)
        {
            sortVec(bddSubResults);
        }
        

        auto toReturn = defaultResult;  
        for (auto& argBdd : bddSubResults) {
            if (isInterrupted()) { return defaultResult; }
            toReturn = op(toReturn, argBdd);
            if (isDefinite(toReturn)) { return toReturn; }   
        }  

        return toReturn;
    }

    BDDInterval getConjunctionBdd(const std::vector<z3::expr>&, const std::vector<boundVar>&, bool, bool);
    BDDInterval getDisjunctionBdd(const std::vector<z3::expr>&, const std::vector<boundVar>&, bool, bool);

    Approximation approximation;
    int variableBitWidth;

    unsigned int operationPrecision;

    ApproximationType approximationType;

    bool variableApproximationHappened = false;
    bool operationApproximationHappened = false;

    int cacheHits = 0;

    Bvec bvec_mul(Bvec&, Bvec&);
    BDDInterval bvec_ule(Bvec&, Bvec&, bool);
    BDDInterval bvec_ult(Bvec&, Bvec&, bool);
    Approximated<Bvec> bvec_assocOp(const z3::expr&, const std::function<Bvec(Bvec, Bvec)>&, const std::vector<boundVar>&);
    Approximated<Bvec> bvec_binOp(const z3::expr&, const std::function<Bvec(Bvec, Bvec)>&, const std::vector<boundVar>&);
    Approximated<Bvec> bvec_unOp(const z3::expr&, const std::function<Bvec(Bvec)>&, const std::vector<boundVar>&);

    Config config;

    void clearCaches();

    template< int n >
    void checkNumberOfArguments(const z3::expr& e)
    {
        if (e.num_args() != n)
        {
            std::cout << e << " -- unsupported number of arguments" << std::endl;
            std::cout << "unknown" << std::endl;
            exit(1);
        }
    }

    bool isInterrupted();

  public:
    ExprToBDDTransformer(z3::context& context, z3::expr e, Config config);

    z3::expr expression;
    BDD Proccess();

    BDDInterval ProcessUnderapproximation(int, unsigned int);
    BDDInterval ProcessOverapproximation(int, unsigned int);

    void setApproximationType(ApproximationType at)
    {
        approximationType = at;
    }

    bool IsPreciseResult()
    {
        return !variableApproximationHappened && !operationApproximationHappened;
    }

    bool VariableApproximationHappened()
    {
        return variableApproximationHappened;
    }

    bool OperationApproximationHappened()
    {
        return operationApproximationHappened;
    }

    void configureReorder()
    {
        if (config.reorderType != NO_REORDER)
        {
          switch (config.reorderType)
          {
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

    void PrintModel(const std::map<std::string, std::vector<bool>>&);
    Model GetModel(BDD);

    void PrintNecessaryValues(BDD);
    void PrintNecessaryVarValues(BDD, const std::string&);
};

#endif
