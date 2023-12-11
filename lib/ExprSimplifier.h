#ifndef EXPRSIMPLIFIER_H
#define EXPRSIMPLIFIER_H
#include "z3++.h"
#include <map>
#include <vector>
#include <set>

#include "SimplificationPass.h"
#include "Model.h"
#include "ExpensiveOp.h"

class ExprSimplifier
{
public:
    ExprSimplifier(z3::context &ctx) :
	propagateUnconstrained(false),
	goalUnconstrained(false)
    {
      this->context = &ctx;
    }

    ExprSimplifier(z3::context &ctx, bool propagateUnconstrained) :
	propagateUnconstrained(propagateUnconstrained),
	goalUnconstrained(false)
    {
      this->context = &ctx;
    }

    ExprSimplifier(z3::context &ctx, bool propagateUnconstrained, bool goalUnconstrained) :
	propagateUnconstrained(propagateUnconstrained),
	goalUnconstrained(goalUnconstrained)
    {
      this->context = &ctx;
    }

    

    z3::expr Simplify (z3::expr);
    z3::expr PushQuantifierIrrelevantSubformulas(const z3::expr&);
    z3::expr RefinedPushQuantifierIrrelevantSubformulas(const z3::expr&);
    z3::expr negate(const z3::expr&);
    bool isSentence(const z3::expr&);
    z3::expr PushNegations(const z3::expr&);
    z3::expr CanonizeBoundVariables(const z3::expr&);
    z3::expr DeCanonizeBoundVariables(const z3::expr&);
    z3::expr StripToplevelExistentials(const z3::expr&);
    z3::expr ReduceDivRem(const z3::expr&);
    z3::expr ReorderAndOrArguments( const z3::expr&, ExprInfo& ); 
    z3::expr GroupExpr(const z3::expr&, ExprInfo&);
    z3::expr GroupConnectiveExpr(const z3::expr_vector&  , ExprInfo&, z3::func_decl );
    bool doOverlap(const std::set<std::string>& ,const std::set<std::string>&);

    void SetProduceModels(const bool value)
    {
        produceModels = value;
    }

    void ReconstructModel(Model &model);

private:
    enum BoundType { EXISTENTIAL, UNIVERSAL };

    struct Var
    {
	std::string name;
	BoundType boundType;
	z3::expr expr;

    Var(std::string name, BoundType boundType, z3::expr e) :
	name(name), boundType(boundType), expr(e)
	    {  }
    };

    std::map<const Z3_ast, z3::expr> refinedPushIrrelevantCache;
    std::map<const Z3_ast, z3::expr> pushIrrelevantCache;
    std::map<std::tuple<const Z3_ast, int, int>, z3::expr> decreaseDeBruijnCache;
    std::map<std::tuple<const Z3_ast, int, int>, bool> isRelevantCache;
    std::map<const Z3_ast, z3::expr> pushNegationsCache;
    std::map<std::string, std::string> canonizeVariableRenaming;
    std::map<const Z3_ast, bool> isSentenceCache;
    std::map<const Z3_ast, z3::expr> reduceDivRemCache;
    void clearCaches();

    z3::context* context;
    z3::expr decreaseDeBruijnIndices(const z3::expr&, int, int);
    bool isRelevant(const z3::expr&, int, int);
    z3::expr mk_or(const z3::expr_vector&) const;
    z3::expr mk_and(const z3::expr_vector&) const ;
    z3::expr modifyQuantifierBody(const z3::expr& quantifierExpr, const z3::expr& newBody) const;
    z3::expr flipQuantifierAndModifyBody(const z3::expr& quantifierExpr, const z3::expr& newBody) const;
    z3::expr applyDer(const z3::expr&) const;

    bool propagateUnconstrained;
    bool goalUnconstrained;
    bool produceModels = false;

    int lastBound = 0;

    std::vector<std::unique_ptr<SimplificationPass>> usedPasses;
};


#endif // EXPRSIMPLIFIER_H
