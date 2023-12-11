#include "ExpensiveOp.h"
#include <set>


using namespace std;
using namespace z3;


std::set<std::string> ExprInfo::getVars(const z3::expr& e) 
{
	if (varsCache.find((Z3_ast)e) != varsCache.end()) 
	{
        return varsCache[(Z3_ast)e];
    }

	if ((e.is_const() && !e.is_numeral()) || e.is_var())
    {
		std::string expressionString = e.to_string();

		if (expressionString == "true" || expressionString == "false")
		{
			// return empty set
			return std::set<std::string>();	
		}
		auto exprSet = std::set<std::string>({e.to_string()});
		varsCache.emplace( (Z3_ast)e , exprSet);
		return exprSet;
	}
	else if (e.is_app())
    {
		func_decl f = e.decl();
		unsigned num = e.num_args();
		auto exprSet = std::set<std::string>();

		for (unsigned i = 0; i < num; i++)
		{
			exprSet.merge(getVars(e.arg(i)));
		}
		varsCache.emplace( (Z3_ast)e , exprSet);
		return exprSet;
    }

	else if(e.is_quantifier())
    {
        auto exprSet = getVars(e.body());
		varsCache.emplace( (Z3_ast)e , exprSet);
		return exprSet;
    }
	// no other expression should be here
	std::cout << e.to_string() << std::endl;
	std::cout << "is var" << e.is_var() << std::endl;
	assert(false);
}


unsigned int ExprInfo::getExpensiveOpNum(const z3::expr&e) {
    /// simply number of expensive opperations in e

    if (expOpCache.find((Z3_ast)e) != expOpCache.end()) 
	{
        return expOpCache[(Z3_ast)e];
    }

    if (e.is_var() || e.is_const()) 
	{
        return 0;
    } 
	else if (e.is_quantifier())
	{
        return getExpensiveOpNum(e.body());
    }
  
	unsigned int exp_ops_sum;
    exp_ops_sum = 0;

	for (auto arg : e.args()) 
	{
		exp_ops_sum += getExpensiveOpNum(arg);
	}
	if (e.is_bv() && e.is_app()) 
	{
		func_decl f = e.decl();
		auto decl_kind = f.decl_kind();
        
		if (expensive_ops_set.find(decl_kind) != expensive_ops_set.end() ) 
		{
			exp_ops_sum += 1;
		}
	}
    expOpCache.insert(std::make_pair((Z3_ast)e, uint(exp_ops_sum)));
    
	return exp_ops_sum;


}

