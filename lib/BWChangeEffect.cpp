#include "BWChangeEffect.h"
#include <iostream>


//@pre: e.is_var() || e.is_const()
void BWChangeEffect::EffectOnVar(const z3::expr &e)
{

}

void BWChangeEffect::ExprWalk(const z3::expr &e)
{
    if (e.is_var() || e.is_const()) {
        // what to do for var

    } else if (e.is_quantifier()) {
        ExprWalk(e.body());

    } else if (e.is_app()) {
        for (int i = 0; i < e.num_args(); ++i) {
            {
                ExprWalk(e.arg(i));
                std::cout << "Arg = " << e.arg(i).to_string() << std::endl;
            }
        }
        if (e.is_bool())
            return;

        z3::func_decl f = e.decl();
        auto decl_kind = f.decl_kind();
        std::cout << "Decl kind = " << decl_kind << std::endl;

    } else {
        std::cout << "else" << std::endl;
    }
}
