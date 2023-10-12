#include <unordered_set>
#include <map>
#include <z3++.h>
#include <iostream>



class ExpensiveOp{

    std::map<Z3_ast, unsigned int> expOpCache;
    const std::unordered_set<Z3_decl_kind> expensive_ops_set {Z3_OP_BMUL,Z3_OP_BUREM,
                                                Z3_OP_BUREM_I , Z3_OP_BSDIV , Z3_OP_BUDIV_I,
                                                Z3_OP_BSDIV, Z3_OP_BSDIV_I, Z3_OP_BSREM,Z3_OP_BSREM_I };

    

public:
    
   
    // number of multiplications and deletions in formula
    unsigned int getExpensiveOpNum(const z3::expr&); 
    
    
    static void printInfo(const z3::expr& e, const unsigned int n) {
        std::cout << "Expression " << e.to_string() << " has " << n << " expensive operations" << std::endl;
    }
};