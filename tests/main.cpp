#define CATCH_CONFIG_MAIN  // This tells Catch to provide a main() - only do this in one cpp file
#include "catch.hpp"
#include "../lib/Solver.h"

#include "../lib/SMTLIBInterpreter.h"

#include "antlr4-runtime.h"
#include "SMTLIBv2Lexer.h"
#include "SMTLIBv2Parser.h"
#include "../lib/BWChangeEffect.h"
#include <vector>

using namespace antlr4;

typedef std::pair<int, int> Interval;

Model model;

Result SolveWithoutApprox(std::string filename)
{
    std::cout << "Without approx: " << filename << std::endl;
    Config config;
    config.propagateUnconstrained = true;
    config.approximationMethod = VARIABLES;
    config.approximations = NO_APPROXIMATIONS;

    std::ifstream stream;
    stream.open(filename);

    ANTLRInputStream input(stream);
    SMTLIBv2Lexer lexer(&input);
    CommonTokenStream tokens(&lexer);
    SMTLIBv2Parser parser{&tokens};

    SMTLIBv2Parser::StartContext* tree = parser.start();

    SMTLIBInterpreter interpreter;
    interpreter.SetConfig(config);

    auto result = interpreter.Run(tree->script());
    if (result == SAT)
    {
        model = interpreter.GetModel();
    }
    return result;
}

Result SolveWithoutApproxLazy(std::string filename)
{
    std::cout << "Without approx & lazy: " << filename << std::endl;
    Config config;
    config.propagateUnconstrained = true;
    config.approximationMethod = VARIABLES;
    config.approximations = NO_APPROXIMATIONS;
    config.lazyEvaluation = true;

    std::ifstream stream;
    stream.open(filename);

    ANTLRInputStream input(stream);
    SMTLIBv2Lexer lexer(&input);
    CommonTokenStream tokens(&lexer);
    SMTLIBv2Parser parser{&tokens};

    SMTLIBv2Parser::StartContext* tree = parser.start();

    SMTLIBInterpreter interpreter;
    interpreter.SetConfig(config);

    auto result = interpreter.Run(tree->script());
    if (result == SAT)
    {
        model = interpreter.GetModel();
    }
    return result;
}


Result SolveWithVariableApprox(std::string filename, Approximation approx = NO_APPROXIMATION)
{
    std::cout << "Var approx: " << filename << std::endl;
    Config config;
    config.propagateUnconstrained = true;
    config.approximationMethod = VARIABLES;
    config.checkModels = false;
    if (approx == UNDERAPPROXIMATION)
        config.approximations = ONLY_UNDERAPPROXIMATIONS;
    else
        config.approximations = ONLY_OVERAPPROXIMATIONS;


    std::ifstream stream;
    stream.open(filename);

    ANTLRInputStream input(stream);
    SMTLIBv2Lexer lexer(&input);
    CommonTokenStream tokens(&lexer);
    SMTLIBv2Parser parser{&tokens};

    SMTLIBv2Parser::StartContext* tree = parser.start();

    SMTLIBInterpreter interpreter;
    interpreter.SetConfig(config);

    return interpreter.Run(tree->script());
}


Result SolveWithVariableApproxLazy(std::string filename, Approximation approx = NO_APPROXIMATION)
{
    std::cout << "Var approx & lazy: " << filename << std::endl;
    Config config;
    config.propagateUnconstrained = true;
    config.approximationMethod = VARIABLES;
    config.checkModels = false;
    config.lazyEvaluation = true;
    if (approx == UNDERAPPROXIMATION)
        config.approximations = ONLY_UNDERAPPROXIMATIONS;
    else
        config.approximations = ONLY_OVERAPPROXIMATIONS;


    std::ifstream stream;
    stream.open(filename);

    ANTLRInputStream input(stream);
    SMTLIBv2Lexer lexer(&input);
    CommonTokenStream tokens(&lexer);
    SMTLIBv2Parser parser{&tokens};

    SMTLIBv2Parser::StartContext* tree = parser.start();

    SMTLIBInterpreter interpreter;
    interpreter.SetConfig(config);

    return interpreter.Run(tree->script());
}

Result SolveWithOperationsLimitApprox(std::string filename, Approximation approx = NO_APPROXIMATION, int precision = 0)
{
    std::cout << "Op approx: " << filename << std::endl;
    Config config;
    config.propagateUnconstrained = true;
    config.approximationMethod = OPERATIONS;
    config.checkModels = true;
    if (approx == UNDERAPPROXIMATION)
        config.approximations = ONLY_UNDERAPPROXIMATIONS;
    else
        config.approximations = ONLY_OVERAPPROXIMATIONS;
    config.precision = precision;

    z3::context ctx;
    z3::solver s(ctx);
    s.from_file(filename.c_str());
    z3::expr expr = mk_and(s.assertions());

    std::ifstream stream;
    stream.open(filename);

    ANTLRInputStream input(stream);
    SMTLIBv2Lexer lexer(&input);
    CommonTokenStream tokens(&lexer);
    SMTLIBv2Parser parser{&tokens};

    SMTLIBv2Parser::StartContext* tree = parser.start();

    SMTLIBInterpreter interpreter;
    interpreter.SetConfig(config);

    return interpreter.Run(tree->script());
}


Result SolveWithOperationsLimitApproxLazy(std::string filename, Approximation approx = NO_APPROXIMATION, int precision = 0)
{
    std::cout << "Op approx & lazy: " << filename << std::endl;
    Config config;
    config.propagateUnconstrained = true;
    config.approximationMethod = OPERATIONS;
    config.checkModels = true;
    config.lazyEvaluation = true;
    if (approx == UNDERAPPROXIMATION)
        config.approximations = ONLY_UNDERAPPROXIMATIONS;
    else
        config.approximations = ONLY_OVERAPPROXIMATIONS;
    config.precision = precision;

    z3::context ctx;
    z3::solver s(ctx);
    s.from_file(filename.c_str());
    z3::expr expr = mk_and(s.assertions());

    std::ifstream stream;
    stream.open(filename);

    ANTLRInputStream input(stream);
    SMTLIBv2Lexer lexer(&input);
    CommonTokenStream tokens(&lexer);
    SMTLIBv2Parser parser{&tokens};

    SMTLIBv2Parser::StartContext* tree = parser.start();

    SMTLIBInterpreter interpreter;
    interpreter.SetConfig(config);

    return interpreter.Run(tree->script());
}

Result SolveWithBothLimitApprox(std::string filename, Approximation approx = NO_APPROXIMATION, int precision = 0)
{
    std::cout << "Both approx: " << filename << std::endl;
    Config config;
    config.propagateUnconstrained = true;
    config.approximationMethod = BOTH;
    config.checkModels = true;
    if (approx == UNDERAPPROXIMATION)
        config.approximations = ONLY_UNDERAPPROXIMATIONS;
    else
        config.approximations = ONLY_OVERAPPROXIMATIONS;
    config.precision = precision;

    std::ifstream stream;
    stream.open(filename);

    ANTLRInputStream input(stream);
    SMTLIBv2Lexer lexer(&input);
    CommonTokenStream tokens(&lexer);
    SMTLIBv2Parser parser{&tokens};

    SMTLIBv2Parser::StartContext* tree = parser.start();

    SMTLIBInterpreter interpreter;
    interpreter.SetConfig(config);
    return interpreter.Run(tree->script());
}


Result SolveWithBothLimitApproxLazy(std::string filename, Approximation approx = NO_APPROXIMATION, int precision = 0)
{
    std::cout << "Both approx & lazy: " << filename << std::endl;
    Config config;
    config.propagateUnconstrained = true;
    config.approximationMethod = BOTH;
    config.checkModels = true;
    config.lazyEvaluation = true;
    if (approx == UNDERAPPROXIMATION)
        config.approximations = ONLY_UNDERAPPROXIMATIONS;
    else
        config.approximations = ONLY_OVERAPPROXIMATIONS;
    config.precision = precision;

    std::ifstream stream;
    stream.open(filename);

    ANTLRInputStream input(stream);
    SMTLIBv2Lexer lexer(&input);
    CommonTokenStream tokens(&lexer);
    SMTLIBv2Parser parser{&tokens};

    SMTLIBv2Parser::StartContext* tree = parser.start();

    SMTLIBInterpreter interpreter;
    interpreter.SetConfig(config);
    return interpreter.Run(tree->script());
}


Result SolveWithoutApproxAndGoalUnconstrained(std::string filename)
{
    Config config;
    config.propagateUnconstrained = true;
    config.goalUnconstrained = true;
    config.approximations = NO_APPROXIMATIONS;

    std::ifstream stream;
    stream.open(filename);

    ANTLRInputStream input(stream);
    SMTLIBv2Lexer lexer(&input);
    CommonTokenStream tokens(&lexer);
    SMTLIBv2Parser parser{&tokens};

    SMTLIBv2Parser::StartContext* tree = parser.start();

    SMTLIBInterpreter interpreter;
    interpreter.SetConfig(config);

    return interpreter.Run(tree->script());
}

Result SolveParallelAndGoalUnconstrained(std::string filename)
{
    Config config;
    config.propagateUnconstrained = true;
    config.goalUnconstrained = true;
    config.approximations = ALL_APPROXIMATIONS;

    std::ifstream stream;
    stream.open(filename);

    ANTLRInputStream input(stream);
    SMTLIBv2Lexer lexer(&input);
    CommonTokenStream tokens(&lexer);
    SMTLIBv2Parser parser{&tokens};

    SMTLIBv2Parser::StartContext* tree = parser.start();

    SMTLIBInterpreter interpreter;
    interpreter.SetConfig(config);

    return interpreter.Run(tree->script());
}


Result SolveParallelAndGoalUnconstrainedLazy(std::string filename)
{
    Config config;
    config.propagateUnconstrained = true;
    config.goalUnconstrained = true;
    config.approximations = ALL_APPROXIMATIONS;
    config.lazyEvaluation = true;
    

    std::ifstream stream;
    stream.open(filename);

    ANTLRInputStream input(stream);
    SMTLIBv2Lexer lexer(&input);
    CommonTokenStream tokens(&lexer);
    SMTLIBv2Parser parser{&tokens};

    SMTLIBv2Parser::StartContext* tree = parser.start();

    SMTLIBInterpreter interpreter;
    interpreter.SetConfig(config);

    return interpreter.Run(tree->script());
}

Result SolveWithAllApproxLazy(std::string filename,  int precision = 0)
{
    std::cout << "Both approx: " << filename << std::endl;
    Config config;
    config.propagateUnconstrained = true;
    config.approximationMethod = BOTH;
    config.checkModels = true;
    config.lazyEvaluation = true;
    config.approximations = ALL_APPROXIMATIONS;
    config.precision = precision;

    std::ifstream stream;
    stream.open(filename);

    ANTLRInputStream input(stream);
    SMTLIBv2Lexer lexer(&input);
    CommonTokenStream tokens(&lexer);
    SMTLIBv2Parser parser{&tokens};

    SMTLIBv2Parser::StartContext* tree = parser.start();

    SMTLIBInterpreter interpreter;
    interpreter.SetConfig(config);
    return interpreter.Run(tree->script());
}



TEST_CASE( "Problematic - Without approximations", "[noapprox]" )
{
    REQUIRE( SolveWithoutApprox("../tests/data/AR-fixpoint-1.smt2") == UNSAT );
    REQUIRE( SolveWithoutApprox("../tests/problematic/188.smt2") == SAT );
    REQUIRE( SolveWithBothLimitApprox("../tests/problematic/188.smt2", OVERAPPROXIMATION) == SAT );
    REQUIRE( SolveWithBothLimitApprox("../tests/problematic/188.smt2", UNDERAPPROXIMATION) == SAT );
    REQUIRE( SolveWithBothLimitApprox("../tests/problematic/vsl.proof-node1722.smt2", OVERAPPROXIMATION) == UNSAT );
    REQUIRE( SolveWithBothLimitApprox("../tests/problematic/check_bvsge_bvand_64bit.smt2", OVERAPPROXIMATION) == UNSAT );
    REQUIRE( SolveWithoutApprox("../tests/problematic/check_bvsge_bvand_64bit.smt2") == UNSAT );
    
    
    
    REQUIRE( SolveWithoutApproxLazy("../tests/data/AR-fixpoint-1.smt2") == UNSAT );
    REQUIRE( SolveWithoutApproxLazy("../tests/problematic/188.smt2") == SAT );
    REQUIRE( SolveWithBothLimitApproxLazy("../tests/problematic/188.smt2", OVERAPPROXIMATION) == SAT );
    REQUIRE( SolveWithBothLimitApproxLazy("../tests/problematic/188.smt2", UNDERAPPROXIMATION) == SAT );
    REQUIRE( SolveWithBothLimitApproxLazy("../tests/problematic/vsl.proof-node1722.smt2", OVERAPPROXIMATION) == UNSAT );
    REQUIRE( SolveWithAllApproxLazy("../tests/problematic/vsl.proof-node1722.smt2") == UNSAT );
    REQUIRE( SolveWithBothLimitApproxLazy("../tests/problematic/check_bvsge_bvand_64bit.smt2", OVERAPPROXIMATION) == UNSAT );
    REQUIRE( SolveWithoutApproxLazy("../tests/problematic/check_bvsge_bvand_64bit.smt2") == UNSAT );
    REQUIRE( SolveWithAllApproxLazy("../tests/problematic/check_bvslt_bvor_64bit-djusted.smt2") == UNSAT );
    
   
}

TEST_CASE( "Wintersteiger - problematic", "[bothlimitapprox]" )
{
    //REQUIRE( SolveWithBothLimitApprox("../tests/wintersteiger/fixpoint-small-pipeline-fixpoint-5.smt2", OVERAPPROXIMATION) == SAT );
    
    //REQUIRE( SolveWithBothLimitApprox("../tests/wintersteiger/fixpoint-small-pipeline-fixpoint-5.smt2", UNDERAPPROXIMATION) == SAT );
    
   
}

TEST_CASE( "Without approximations", "[noapprox]" )
{
    REQUIRE( SolveWithoutApprox("../tests/data/AR-fixpoint-1.smt2") == UNSAT );
    REQUIRE( SolveWithoutApprox("../tests/data/cache-coherence-2-fixpoint-1.smt2") == UNSAT );
    REQUIRE( SolveWithoutApprox("../tests/data/itc-b13-fixpoint-3.smt2") == SAT );
    REQUIRE( SolveWithoutApprox("../tests/data/Fibonacci01_true-unreach-call_true-no-overflow.c_905.smt2") == SAT );
    REQUIRE( SolveWithoutApprox("../tests/data/nlzbe008.smt2") == UNSAT );
    REQUIRE( SolveWithoutApprox("../tests/data/falseAndFalse.smt2") == UNSAT );
    REQUIRE( SolveWithoutApprox("../tests/data/bvshl0.smt2") == SAT );
    REQUIRE( SolveWithoutApprox("../tests/data/check_bvsge_bvashr0_16bit.smt2") == UNSAT );
    REQUIRE( SolveWithoutApprox("../tests/data/magnetic_field-node118398.smt2") == UNSAT );
    REQUIRE( SolveWithoutApprox("../tests/data/unconstrainedMulVar.smt2") == UNSAT );
    REQUIRE( SolveWithoutApprox("../tests/data/check_bvsle_bvmul_8bit.smt2") == UNSAT );
    REQUIRE( SolveWithoutApprox("../tests/data/unconstrainedMulConst.smt2") == SAT );
    REQUIRE( SolveWithoutApprox("../tests/data/check_eq_bvconcat0_2_64bit.smt2") == UNSAT );
    REQUIRE( SolveWithoutApprox("../tests/data/002.smt2") == UNSAT );
    REQUIRE( SolveWithoutApprox("../tests/data/MADWiFi-encode_ie_ok_true-unreach-call.i_7.smt2") == UNSAT );
    REQUIRE( SolveWithoutApprox("../tests/data/usb-phy-fixpoint-1.smt2") == UNSAT );
    REQUIRE( SolveWithoutApprox("../tests/data/pi-bus-fixpoint-1.smt2") == UNSAT );
    REQUIRE( SolveWithoutApprox("../tests/data/check_eq_bvshl0_32bit.smt2") == UNSAT );
    REQUIRE( SolveWithoutApprox("../tests/data/check_bvuge_bvashr1_64bit.smt2") == UNSAT );
    REQUIRE( SolveWithoutApprox("../tests/data/preiner_bug_2020.smt2") == UNSAT );
    REQUIRE( SolveWithoutApprox("../tests/data/smtcomp23/heapsort.i_0.smt2") == UNSAT );
    REQUIRE( SolveWithoutApprox("../tests/data/smtcomp23/heapsort.i_3.smt2") == UNSAT );
    REQUIRE( SolveWithoutApprox("../tests/data/smtcomp23/heapsort.i_8.smt2") == UNSAT );
    REQUIRE( SolveWithoutApprox("../tests/data/smtcomp23/heapsort.i_9.smt2") == UNSAT );
    REQUIRE( SolveWithoutApprox("../tests/data/smtcomp23/minimal.smt2") == UNSAT );
}

TEST_CASE( "Without approximations -- lazy", "[noapprox]" )
{
    REQUIRE( SolveWithoutApproxLazy("../tests/data/AR-fixpoint-1.smt2") == UNSAT );
    REQUIRE( SolveWithoutApproxLazy("../tests/data/cache-coherence-2-fixpoint-1.smt2") == UNSAT );
    REQUIRE( SolveWithoutApproxLazy("../tests/data/itc-b13-fixpoint-3.smt2") == SAT );
    REQUIRE( SolveWithoutApproxLazy("../tests/data/Fibonacci01_true-unreach-call_true-no-overflow.c_905.smt2") == SAT );
    REQUIRE( SolveWithoutApproxLazy("../tests/data/nlzbe008.smt2") == UNSAT );
    REQUIRE( SolveWithoutApproxLazy("../tests/data/falseAndFalse.smt2") == UNSAT );
    REQUIRE( SolveWithoutApproxLazy("../tests/data/bvshl0.smt2") == SAT );
    REQUIRE( SolveWithoutApproxLazy("../tests/data/check_bvsge_bvashr0_16bit.smt2") == UNSAT );
    REQUIRE( SolveWithoutApproxLazy("../tests/data/magnetic_field-node118398.smt2") == UNSAT );
    REQUIRE( SolveWithoutApproxLazy("../tests/data/unconstrainedMulVar.smt2") == UNSAT );
    REQUIRE( SolveWithoutApproxLazy("../tests/data/check_bvsle_bvmul_8bit.smt2") == UNSAT );
    REQUIRE( SolveWithoutApproxLazy("../tests/data/unconstrainedMulConst.smt2") == SAT );
    REQUIRE( SolveWithoutApproxLazy("../tests/data/check_eq_bvconcat0_2_64bit.smt2") == UNSAT );
    REQUIRE( SolveWithoutApproxLazy("../tests/data/002.smt2") == UNSAT );
    REQUIRE( SolveWithoutApproxLazy("../tests/data/MADWiFi-encode_ie_ok_true-unreach-call.i_7.smt2") == UNSAT );
    REQUIRE( SolveWithoutApproxLazy("../tests/data/usb-phy-fixpoint-1.smt2") == UNSAT );
    REQUIRE( SolveWithoutApproxLazy("../tests/data/pi-bus-fixpoint-1.smt2") == UNSAT );
    REQUIRE( SolveWithoutApproxLazy("../tests/data/check_eq_bvshl0_32bit.smt2") == UNSAT );
    REQUIRE( SolveWithoutApproxLazy("../tests/data/check_bvuge_bvashr1_64bit.smt2") == UNSAT );
    REQUIRE( SolveWithoutApproxLazy("../tests/data/preiner_bug_2020.smt2") == UNSAT );
    REQUIRE( SolveWithoutApproxLazy("../tests/data/smtcomp23/heapsort.i_0.smt2") == UNSAT );
    REQUIRE( SolveWithoutApproxLazy("../tests/data/smtcomp23/heapsort.i_3.smt2") == UNSAT );
    REQUIRE( SolveWithoutApproxLazy("../tests/data/smtcomp23/heapsort.i_8.smt2") == UNSAT );
    REQUIRE( SolveWithoutApproxLazy("../tests/data/smtcomp23/heapsort.i_9.smt2") == UNSAT );
    REQUIRE( SolveWithoutApproxLazy("../tests/data/smtcomp23/minimal.smt2") == UNSAT );
}

TEST_CASE( "With variable approximations", "[variableapprox]" )
{
    REQUIRE( SolveWithVariableApprox("../tests/data/audio_ac97_wavepcistream2.cpp.smt2", OVERAPPROXIMATION) == UNSAT );
    REQUIRE( SolveWithVariableApprox("../tests/data/jain_7_true-unreach-call_true-no-overflow.i_61.smt2", OVERAPPROXIMATION) == UNSAT );
    REQUIRE( SolveWithVariableApprox("../tests/data/RNDPRE_3_48.smt2", UNDERAPPROXIMATION) == SAT );
    REQUIRE( SolveWithVariableApprox("../tests/data/ETCS-essentials-node3023.smt2", UNDERAPPROXIMATION) == SAT );
    REQUIRE( SolveWithVariableApprox("../tests/data/accelerating-node2100.smt2", UNDERAPPROXIMATION) == SAT );
    REQUIRE( SolveWithVariableApprox("../tests/data/binary_driver-2007-10-09-node11383.smt2", UNDERAPPROXIMATION) == SAT );
    REQUIRE( SolveWithVariableApprox("../tests/data/ARI118=1.smt2", OVERAPPROXIMATION) == UNSAT );
}

TEST_CASE( "With variable approximations -- lazy", "[variableapprox]" )
{
    REQUIRE( SolveWithVariableApproxLazy("../tests/data/audio_ac97_wavepcistream2.cpp.smt2", OVERAPPROXIMATION) == UNSAT );
    REQUIRE( SolveWithVariableApproxLazy("../tests/data/jain_7_true-unreach-call_true-no-overflow.i_61.smt2", OVERAPPROXIMATION) == UNSAT );
    REQUIRE( SolveWithVariableApproxLazy("../tests/data/RNDPRE_3_48.smt2", UNDERAPPROXIMATION) == SAT );
    REQUIRE( SolveWithVariableApproxLazy("../tests/data/ETCS-essentials-node3023.smt2", UNDERAPPROXIMATION) == SAT );
    REQUIRE( SolveWithVariableApproxLazy("../tests/data/accelerating-node2100.smt2", UNDERAPPROXIMATION) == SAT );
    REQUIRE( SolveWithVariableApproxLazy("../tests/data/binary_driver-2007-10-09-node11383.smt2", UNDERAPPROXIMATION) == SAT );
    REQUIRE( SolveWithVariableApproxLazy("../tests/data/ARI118=1.smt2", OVERAPPROXIMATION) == UNSAT );
}

TEST_CASE( "With bothLimit approximations", "[bothlimitapprox]" )
{
    REQUIRE( SolveWithBothLimitApprox("../tests/data/RNDPRE_4_42.smt2", OVERAPPROXIMATION) == UNSAT );
    REQUIRE( SolveWithBothLimitApprox("../tests/data/RND_6_4.smt2", UNDERAPPROXIMATION) == SAT );
    REQUIRE( SolveWithBothLimitApprox("../tests/data/jain_7_true-unreach-call_true-no-overflow.i_61.smt2", OVERAPPROXIMATION) == UNSAT );

    //correct model returned by an overapproximation
    REQUIRE( SolveWithBothLimitApprox("../tests/data/007.smt2", OVERAPPROXIMATION) == SAT );
    REQUIRE( SolveWithBothLimitApprox("../tests/data/sum02_true-unreach-call_true-no-overflow.i_375.smt2", OVERAPPROXIMATION) == SAT );
    REQUIRE( SolveWithBothLimitApprox("../tests/data/check_bvsgt_bvudiv1_8bit.smt2", UNDERAPPROXIMATION) != SAT );
    REQUIRE( SolveWithBothLimitApprox("../tests/data/bvurem_approx.smt2", UNDERAPPROXIMATION, 1) != SAT );
}

TEST_CASE( "With bothLimit approximations -- lazy", "[bothlimitapprox]" )
{
    REQUIRE( SolveWithBothLimitApproxLazy("../tests/data/RNDPRE_4_42.smt2", OVERAPPROXIMATION) == UNSAT );
    REQUIRE( SolveWithBothLimitApproxLazy("../tests/data/RND_6_4.smt2", UNDERAPPROXIMATION) == SAT );
    REQUIRE( SolveWithBothLimitApproxLazy("../tests/data/jain_7_true-unreach-call_true-no-overflow.i_61.smt2", OVERAPPROXIMATION) == UNSAT );

    //correct model returned by an overapproximation
    REQUIRE( SolveWithBothLimitApproxLazy("../tests/data/007.smt2", OVERAPPROXIMATION) == SAT );
    REQUIRE( SolveWithBothLimitApproxLazy("../tests/data/sum02_true-unreach-call_true-no-overflow.i_375.smt2", OVERAPPROXIMATION) == SAT );
    REQUIRE( SolveWithBothLimitApproxLazy("../tests/data/check_bvsgt_bvudiv1_8bit.smt2", UNDERAPPROXIMATION) != SAT );
    REQUIRE( SolveWithBothLimitApproxLazy("../tests/data/bvurem_approx.smt2", UNDERAPPROXIMATION, 1) != SAT );
}


TEST_CASE( "With bothLimit approximations -- term introducer ", "[bothlimitapprox-ti]" )
{
    REQUIRE( SolveWithBothLimitApprox("../tests/data/intersection-example-onelane.proof-node1469.smt2", OVERAPPROXIMATION) == UNSAT );
}

TEST_CASE( "With operation approximations -- ite ", "[opapproxlimit-ite]" )
{
    REQUIRE( SolveWithOperationsLimitApprox("../tests/data/iteApprox.smt2", UNDERAPPROXIMATION, 1) != UNSAT );
}

TEST_CASE( "With parallel approximations", "[parallel]" )
{
    REQUIRE( SolveParallelAndGoalUnconstrained ("../tests/data/003.smt2") == SAT );
}

TEST_CASE( "With parallel approximations --lazy", "[parallel]" )
{
    REQUIRE( SolveParallelAndGoalUnconstrainedLazy ("../tests/data/003.smt2") == SAT );
}

TEST_CASE( "SMT-COMP 2018", "[smtcomp18]" )
{
    REQUIRE( SolveWithVariableApprox( "../tests/data/smtcomp18/01.smt2", UNDERAPPROXIMATION ) != SAT );
    REQUIRE( SolveWithBothLimitApprox( "../tests/data/smtcomp18/02.smt2", OVERAPPROXIMATION, 1 ) != UNSAT );
}




TEST_CASE( "SMT-COMP 2018 --lazy", "[smtcomp18]" )
{
    REQUIRE( SolveWithVariableApproxLazy( "../tests/data/smtcomp18/01.smt2", UNDERAPPROXIMATION ) != SAT );
    REQUIRE( SolveWithBothLimitApproxLazy( "../tests/data/smtcomp18/02.smt2", OVERAPPROXIMATION, 1 ) != UNSAT );
}

TEST_CASE( "Without approximations -- goal unconstrained", "[goalunconstrained]" )
{
    REQUIRE( SolveWithoutApproxAndGoalUnconstrained( "../tests/data/check_bvuge_bvudiv0_4bit.smt2" ) != SAT );
    REQUIRE( SolveWithoutApproxAndGoalUnconstrained( "../tests/data/check_bvugt_bvshl0_4bit.smt2" ) != SAT );
    REQUIRE( SolveWithoutApproxAndGoalUnconstrained( "../tests/data/check_bvsle_bvlshr0_4bit.smt2" ) != SAT );
    REQUIRE( SolveWithoutApproxAndGoalUnconstrained( "../tests/data/check_bvsle_bvashr0_4bit.smt2" ) != SAT );
    REQUIRE( SolveWithoutApproxAndGoalUnconstrained( "../tests/data/check_bvslt_bvashr0_4bit.smt2" ) != SAT );
}



TEST_CASE( "SMT-LIB", "[smtlib]" )
{
    REQUIRE( SolveWithoutApproxAndGoalUnconstrained( "../tests/data/smtlib/binaryNumeral.smt2" ) == SAT );
    REQUIRE( SolveWithoutApproxAndGoalUnconstrained( "../tests/data/smtlib/hexNumeral.smt2" ) == SAT );
    REQUIRE( SolveWithoutApproxAndGoalUnconstrained( "../tests/data/smtlib/push.smt2" ) == SAT );
    REQUIRE( SolveWithoutApproxAndGoalUnconstrained( "../tests/data/smtlib/pushPush.smt2" ) == UNSAT );
    REQUIRE( SolveWithoutApproxAndGoalUnconstrained( "../tests/data/smtlib/pushPushPop.smt2" ) == SAT );
    REQUIRE( SolveWithoutApproxAndGoalUnconstrained( "../tests/data/smtlib/push2Pop.smt2" ) == UNSAT );
    REQUIRE( SolveWithoutApproxAndGoalUnconstrained( "../tests/data/smtlib/push2Pop2.smt2" ) == SAT);
    REQUIRE( SolveWithoutApproxAndGoalUnconstrained( "../tests/data/smtlib/reset.smt2" ) == SAT);
    REQUIRE( SolveWithoutApproxAndGoalUnconstrained( "../tests/data/smtlib/resetAssertions.smt2" ) == SAT);
}

TEST_CASE( "Models", "[models]" )
{
    REQUIRE( SolveWithoutApprox( "../tests/data/smtlib/model1.smt2" ) == SAT );
    REQUIRE( model.find("x") != model.end() );
    REQUIRE( std::get<1>(model["x"]) == std::vector<bool>{false, false, false, true} );

    REQUIRE( SolveWithoutApprox( "../tests/data/smtlib/model2.smt2" ) == SAT );
    REQUIRE( model.find("x") != model.end() );
    REQUIRE( model.find("y") != model.end() );
    REQUIRE( model.find("z") != model.end() );
    REQUIRE( std::get<1>(model["x"]) == std::vector<bool>{false, false, false, true} );
    REQUIRE( std::get<1>(model["y"]) == std::vector<bool>{false, false, false, true} );
    REQUIRE( std::get<1>(model["z"]) == std::vector<bool>{false, false, true, false} );

    REQUIRE( SolveWithoutApprox( "../tests/data/smtlib/model3.smt2" ) == SAT );
    REQUIRE( model.find("x") != model.end() );
    REQUIRE( model.find("y") != model.end() );
    REQUIRE( model.find("z") != model.end() );
    REQUIRE( std::get<1>(model["x"]) == std::vector<bool>{false, false, true, true} );
    REQUIRE( std::get<1>(model["y"]) == std::vector<bool>{false, false, true, true} );
    REQUIRE( std::get<1>(model["z"]) == std::vector<bool>{true, false, false, true} );
}



std::vector<Interval> getRightShift(const std::vector<Interval>& vec, unsigned int offset) 
{
    return BWChangeEffect::ShiftRight(vec , offset);
}

std::vector<Interval> getLefttShift(const std::vector<Interval>& vec, unsigned int offset) 
{
    return BWChangeEffect::ShiftLeft(vec , offset);
}

TEST_CASE("Right Shift Test")
{
	
	// CASE 1
	std::vector<Interval> vec ={{4,2}};
	std::vector<Interval> res ={{2,0}};
	std::vector<Interval> res_overflow ={{1,0}};
	std::vector<Interval> res_full_overflow = {};
		
	REQUIRE (getRightShift(vec, 2) == res);
	REQUIRE (getRightShift(vec, 0) == vec);
	REQUIRE (getRightShift(vec, 3) == res_overflow );
	REQUIRE (getRightShift(vec, 12) == res_full_overflow );
	
	// CASE 2
	std::vector<Interval> vec2 ={{INT_MAX,2}};
	std::vector<Interval> res2 ={{INT_MAX,0}};
	
	REQUIRE (getRightShift(vec2, 2) == res2);
	REQUIRE (getRightShift(vec2, 5) == res2);
	
	// CASE 3
	std::vector<Interval> vec3 ={{INT_MAX,0}};
	std::vector<Interval> res3 ={{INT_MAX,0}};
	
	REQUIRE (getRightShift(vec3, 2) == res3);
	REQUIRE (getRightShift(vec3, 5) == res3);
}

TEST_CASE("Left Shift Test")
{
	
	// CASE 1
	std::vector<Interval> vec ={{4,2}};
	std::vector<Interval> res ={{6,4}};
		
	REQUIRE (getLefttShift(vec, 2) == res);
	REQUIRE (getLefttShift(vec, 0) == vec);
	
	// CASE 2
	std::vector<Interval> vec2 ={{INT_MAX,2}};
	std::vector<Interval> res2 ={{INT_MAX,4}};
	
	REQUIRE (getLefttShift(vec2, 2) == res2);
	
	// CASE 3
	std::vector<Interval> vec3 ={{INT_MAX,0}};
	std::vector<Interval> res3 ={{INT_MAX,2}};
	
	REQUIRE (getLefttShift(vec3, 2) == res3);
}

TEST_CASE(" Shift Test")
{
	
	// CASE 1
	std::vector<Interval> vec ={{4,2}};
	std::vector<Interval> res =BWChangeEffect::EffectOfShift(vec, 2);
	std::vector<Interval> res_right = {{3,1}};
		
	REQUIRE (getLefttShift(vec, 2) == res);
	REQUIRE (BWChangeEffect::EffectOfShift(vec, 0) == vec);
	REQUIRE (BWChangeEffect::EffectOfShift(vec, -1) == res_right);
	
	// CASE 2
	std::vector<Interval> vec2 ={{INT_MAX,2}};
	std::vector<Interval> res2 ={{INT_MAX,4}};
	std::vector<Interval> res2_overflow ={{INT_MAX,0}};
	
	
	REQUIRE (BWChangeEffect::EffectOfShift(vec2, 2) == res2);
	REQUIRE (BWChangeEffect::EffectOfShift(vec2, -3) == res2_overflow);
	
	// CASE 3
	std::vector<Interval> vec3 ={{INT_MAX,0}};
	std::vector<Interval> res3 ={{INT_MAX,2}};
	
	REQUIRE (BWChangeEffect::EffectOfShift(vec3, 2) == res3);
	REQUIRE (BWChangeEffect::EffectOfShift(vec3, -2) == vec3);
	
}


TEST_CASE(" Extract Test")
{	
	// CASE 1 extract [5, 0]
	std::vector<Interval> vec ={{7,2}};
	std::vector<Interval> res ={{5,2}};
	REQUIRE(BWChangeEffect::EffectOnExtract(vec, 0, 6) == res);
	
	// CASE 2 extract [5, 3]
	std::vector<Interval> vec2 ={{7,2}};
	std::vector<Interval> res2 ={{2,0}};
	REQUIRE(BWChangeEffect::EffectOnExtract(vec2, 3, 3) == res2);
	
	// CASE 3 extract [7,5]
	
	std::vector<Interval> vec3 ={{7,2}};
	std::vector<Interval> res3 ={{2, 0}};
	REQUIRE(BWChangeEffect::EffectOnExtract(vec3, 5, 3) == res3);
	
	
	// CASE 4 extract [7, 0]
	
	std::vector<Interval> vec4 ={{7,2}};
	std::vector<Interval> res4 ={{7,2}};
	REQUIRE(BWChangeEffect::EffectOnExtract(vec4, 0, 8) == res4);
	
	// CASE 5 extraxt [4,1]
	std::vector<Interval> vec5 ={{INT_MAX,0}};
	std::vector<Interval> res5 ={{3,0}};
	
	REQUIRE(BWChangeEffect::EffectOnExtract(vec5, 1, 4) == res5);
	
	// CASE 6 extraxt [4,1]
	std::vector<Interval> vec6 ={{INT_MAX,0}};
	std::vector<Interval> res6={{3,0}};
	
	REQUIRE(BWChangeEffect::EffectOnExtract(vec6, 1, 4) == res6);
	
	// CASE 7 extract [5, 0]
	std::vector<Interval> vec7 ={{7,6}, {1, 0}};
	std::vector<Interval> res7={{1,0}};
	
	REQUIRE(BWChangeEffect::EffectOnExtract(vec7, 0, 6) == res7);
	
	// CASE 8 extract [5, 3]
	std::vector<Interval> vec8 ={{7,6}, {1, 0}};
	std::vector<Interval> res8={};
	
	REQUIRE(BWChangeEffect::EffectOnExtract(vec8, 3, 3) == res8);
	
}
