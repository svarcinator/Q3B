#include "ExpensiveOp.h"


using namespace std;
using namespace z3;



unsigned int ExpensiveOp::getExpensiveOpNum(const z3::expr&e) {
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
			if (decl_kind == Z3_OP_BMUL) {
				exp_ops_sum += 1;
				exp_ops_sum *= 5;
			} else {
				exp_ops_sum += 1;
			}
			
		}
	}
    expOpCache.insert(std::make_pair((Z3_ast)e, uint(exp_ops_sum)));
    
	return exp_ops_sum;


}

