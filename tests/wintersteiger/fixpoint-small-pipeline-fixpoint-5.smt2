(set-info :smt-lib-version 2.6)
(set-logic BV)
(set-info :source | 
Hardware fixpoint check problems.
These benchmarks stem from an evaluation described in Wintersteiger, Hamadi, de Moura: Efficiently solving quantified bit-vector formulas, FMSD 42(1), 2013.
The hardware models that were used are from the VCEGAR benchmark suite (see www.cprover.org/hardware/).
 |)
(set-info :category "industrial")
(set-info :status unknown)
(assert (forall ((Verilog__main.dataOut_64_0 (_ BitVec 32))) (forall ((Verilog__main.stageOne_64_0 (_ BitVec 32))) (forall ((Verilog__main.stageTwo_64_0 (_ BitVec 32))) (forall ((Verilog__main.tmp_stageOne_64_0 (_ BitVec 32))) (forall ((Verilog__main.tmp_stageTwo_64_0 (_ BitVec 32))) (forall ((Verilog__main.dataOut_64_1 (_ BitVec 32))) (forall ((Verilog__main.reset_64_0 Bool)) (forall ((Verilog__main.stageOne_64_1 (_ BitVec 32))) (forall ((Verilog__main.dataIn_64_0 (_ BitVec 32))) (forall ((Verilog__main.c1_64_0 (_ BitVec 32))) (forall ((Verilog__main.stageTwo_64_1 (_ BitVec 32))) (forall ((Verilog__main.c2_64_0 (_ BitVec 32))) (forall ((Verilog__main.tmp_stageOne_64_1 (_ BitVec 32))) (forall ((Verilog__main.tmp_stageTwo_64_1 (_ BitVec 32))) (forall ((Verilog__main.dataOut_64_2 (_ BitVec 32))) (forall ((Verilog__main.reset_64_1 Bool)) (forall ((Verilog__main.stageOne_64_2 (_ BitVec 32))) (forall ((Verilog__main.dataIn_64_1 (_ BitVec 32))) (forall ((Verilog__main.c1_64_1 (_ BitVec 32))) (forall ((Verilog__main.stageTwo_64_2 (_ BitVec 32))) (forall ((Verilog__main.c2_64_1 (_ BitVec 32))) (forall ((Verilog__main.tmp_stageOne_64_2 (_ BitVec 32))) (forall ((Verilog__main.tmp_stageTwo_64_2 (_ BitVec 32))) (forall ((Verilog__main.dataOut_64_3 (_ BitVec 32))) (forall ((Verilog__main.reset_64_2 Bool)) (forall ((Verilog__main.stageOne_64_3 (_ BitVec 32))) (forall ((Verilog__main.dataIn_64_2 (_ BitVec 32))) (forall ((Verilog__main.c1_64_2 (_ BitVec 32))) (forall ((Verilog__main.stageTwo_64_3 (_ BitVec 32))) (forall ((Verilog__main.c2_64_2 (_ BitVec 32))) (forall ((Verilog__main.tmp_stageOne_64_3 (_ BitVec 32))) (forall ((Verilog__main.tmp_stageTwo_64_3 (_ BitVec 32))) (forall ((Verilog__main.dataOut_64_4 (_ BitVec 32))) (forall ((Verilog__main.reset_64_3 Bool)) (forall ((Verilog__main.stageOne_64_4 (_ BitVec 32))) (forall ((Verilog__main.dataIn_64_3 (_ BitVec 32))) (forall ((Verilog__main.c1_64_3 (_ BitVec 32))) (forall ((Verilog__main.stageTwo_64_4 (_ BitVec 32))) (forall ((Verilog__main.c2_64_3 (_ BitVec 32))) (forall ((Verilog__main.tmp_stageOne_64_4 (_ BitVec 32))) (forall ((Verilog__main.tmp_stageTwo_64_4 (_ BitVec 32))) (forall ((Verilog__main.dataOut_64_5 (_ BitVec 32))) (forall ((Verilog__main.reset_64_4 Bool)) (forall ((Verilog__main.stageOne_64_5 (_ BitVec 32))) (forall ((Verilog__main.dataIn_64_4 (_ BitVec 32))) (forall ((Verilog__main.c1_64_4 (_ BitVec 32))) (forall ((Verilog__main.stageTwo_64_5 (_ BitVec 32))) (forall ((Verilog__main.c2_64_4 (_ BitVec 32))) (forall ((Verilog__main.tmp_stageOne_64_5 (_ BitVec 32))) (forall ((Verilog__main.tmp_stageTwo_64_5 (_ BitVec 32))) (exists ((Verilog__main.dataOut_64_0_39_ (_ BitVec 32))) (exists ((Verilog__main.stageOne_64_0_39_ (_ BitVec 32))) (exists ((Verilog__main.stageTwo_64_0_39_ (_ BitVec 32))) (exists ((Verilog__main.tmp_stageOne_64_0_39_ (_ BitVec 32))) (exists ((Verilog__main.tmp_stageTwo_64_0_39_ (_ BitVec 32))) (exists ((Verilog__main.dataOut_64_1_39_ (_ BitVec 32))) (exists ((Verilog__main.reset_64_0_39_ Bool)) (exists ((Verilog__main.stageOne_64_1_39_ (_ BitVec 32))) (exists ((Verilog__main.dataIn_64_0_39_ (_ BitVec 32))) (exists ((Verilog__main.c1_64_0_39_ (_ BitVec 32))) (exists ((Verilog__main.stageTwo_64_1_39_ (_ BitVec 32))) (exists ((Verilog__main.c2_64_0_39_ (_ BitVec 32))) (exists ((Verilog__main.tmp_stageOne_64_1_39_ (_ BitVec 32))) (exists ((Verilog__main.tmp_stageTwo_64_1_39_ (_ BitVec 32))) (exists ((Verilog__main.dataOut_64_2_39_ (_ BitVec 32))) (exists ((Verilog__main.reset_64_1_39_ Bool)) (exists ((Verilog__main.stageOne_64_2_39_ (_ BitVec 32))) (exists ((Verilog__main.dataIn_64_1_39_ (_ BitVec 32))) (exists ((Verilog__main.c1_64_1_39_ (_ BitVec 32))) (exists ((Verilog__main.stageTwo_64_2_39_ (_ BitVec 32))) (exists ((Verilog__main.c2_64_1_39_ (_ BitVec 32))) (exists ((Verilog__main.tmp_stageOne_64_2_39_ (_ BitVec 32))) (exists ((Verilog__main.tmp_stageTwo_64_2_39_ (_ BitVec 32))) (exists ((Verilog__main.dataOut_64_3_39_ (_ BitVec 32))) (exists ((Verilog__main.reset_64_2_39_ Bool)) (exists ((Verilog__main.stageOne_64_3_39_ (_ BitVec 32))) (exists ((Verilog__main.dataIn_64_2_39_ (_ BitVec 32))) (exists ((Verilog__main.c1_64_2_39_ (_ BitVec 32))) (exists ((Verilog__main.stageTwo_64_3_39_ (_ BitVec 32))) (exists ((Verilog__main.c2_64_2_39_ (_ BitVec 32))) (exists ((Verilog__main.tmp_stageOne_64_3_39_ (_ BitVec 32))) (exists ((Verilog__main.tmp_stageTwo_64_3_39_ (_ BitVec 32))) (exists ((Verilog__main.dataOut_64_4_39_ (_ BitVec 32))) (exists ((Verilog__main.reset_64_3_39_ Bool)) (exists ((Verilog__main.stageOne_64_4_39_ (_ BitVec 32))) (exists ((Verilog__main.dataIn_64_3_39_ (_ BitVec 32))) (exists ((Verilog__main.c1_64_3_39_ (_ BitVec 32))) (exists ((Verilog__main.stageTwo_64_4_39_ (_ BitVec 32))) (exists ((Verilog__main.c2_64_3_39_ (_ BitVec 32))) (exists ((Verilog__main.tmp_stageOne_64_4_39_ (_ BitVec 32))) (exists ((Verilog__main.tmp_stageTwo_64_4_39_ (_ BitVec 32))) (=> (and (and (= Verilog__main.dataOut_64_0 (_ bv0 32)) (= Verilog__main.stageOne_64_0 (_ bv0 32)) (= Verilog__main.stageTwo_64_0 (_ bv0 32)) (= Verilog__main.tmp_stageOne_64_0 (_ bv0 32)) (= Verilog__main.tmp_stageTwo_64_0 (_ bv0 32))) (and (= Verilog__main.dataOut_64_1 (ite (not Verilog__main.reset_64_0) (bvadd Verilog__main.stageTwo_64_0 Verilog__main.stageOne_64_0) (_ bv0 32))) (= Verilog__main.stageOne_64_1 (bvadd Verilog__main.dataIn_64_0 Verilog__main.c1_64_0)) (= Verilog__main.stageTwo_64_1 (bvand Verilog__main.stageOne_64_0 Verilog__main.c2_64_0)) (= Verilog__main.tmp_stageOne_64_1 Verilog__main.stageOne_64_0) (= Verilog__main.tmp_stageTwo_64_1 Verilog__main.stageTwo_64_0)) (and (= Verilog__main.dataOut_64_2 (ite (not Verilog__main.reset_64_1) (bvadd Verilog__main.stageTwo_64_1 Verilog__main.stageOne_64_1) (_ bv0 32))) (= Verilog__main.stageOne_64_2 (bvadd Verilog__main.dataIn_64_1 Verilog__main.c1_64_1)) (= Verilog__main.stageTwo_64_2 (bvand Verilog__main.stageOne_64_1 Verilog__main.c2_64_1)) (= Verilog__main.tmp_stageOne_64_2 Verilog__main.stageOne_64_1) (= Verilog__main.tmp_stageTwo_64_2 Verilog__main.stageTwo_64_1)) (and (= Verilog__main.dataOut_64_3 (ite (not Verilog__main.reset_64_2) (bvadd Verilog__main.stageTwo_64_2 Verilog__main.stageOne_64_2) (_ bv0 32))) (= Verilog__main.stageOne_64_3 (bvadd Verilog__main.dataIn_64_2 Verilog__main.c1_64_2)) (= Verilog__main.stageTwo_64_3 (bvand Verilog__main.stageOne_64_2 Verilog__main.c2_64_2)) (= Verilog__main.tmp_stageOne_64_3 Verilog__main.stageOne_64_2) (= Verilog__main.tmp_stageTwo_64_3 Verilog__main.stageTwo_64_2)) (and (= Verilog__main.dataOut_64_4 (ite (not Verilog__main.reset_64_3) (bvadd Verilog__main.stageTwo_64_3 Verilog__main.stageOne_64_3) (_ bv0 32))) (= Verilog__main.stageOne_64_4 (bvadd Verilog__main.dataIn_64_3 Verilog__main.c1_64_3)) (= Verilog__main.stageTwo_64_4 (bvand Verilog__main.stageOne_64_3 Verilog__main.c2_64_3)) (= Verilog__main.tmp_stageOne_64_4 Verilog__main.stageOne_64_3) (= Verilog__main.tmp_stageTwo_64_4 Verilog__main.stageTwo_64_3)) (and (= Verilog__main.dataOut_64_5 (ite (not Verilog__main.reset_64_4) (bvadd Verilog__main.stageTwo_64_4 Verilog__main.stageOne_64_4) (_ bv0 32))) (= Verilog__main.stageOne_64_5 (bvadd Verilog__main.dataIn_64_4 Verilog__main.c1_64_4)) (= Verilog__main.stageTwo_64_5 (bvand Verilog__main.stageOne_64_4 Verilog__main.c2_64_4)) (= Verilog__main.tmp_stageOne_64_5 Verilog__main.stageOne_64_4) (= Verilog__main.tmp_stageTwo_64_5 Verilog__main.stageTwo_64_4))) (and (and (and (= Verilog__main.dataOut_64_0_39_ (_ bv0 32)) (= Verilog__main.stageOne_64_0_39_ (_ bv0 32)) (= Verilog__main.stageTwo_64_0_39_ (_ bv0 32)) (= Verilog__main.tmp_stageOne_64_0_39_ (_ bv0 32)) (= Verilog__main.tmp_stageTwo_64_0_39_ (_ bv0 32))) (and (= Verilog__main.dataOut_64_1_39_ (ite (not Verilog__main.reset_64_0_39_) (bvadd Verilog__main.stageTwo_64_0_39_ Verilog__main.stageOne_64_0_39_) (_ bv0 32))) (= Verilog__main.stageOne_64_1_39_ (bvadd Verilog__main.dataIn_64_0_39_ Verilog__main.c1_64_0_39_)) (= Verilog__main.stageTwo_64_1_39_ (bvand Verilog__main.stageOne_64_0_39_ Verilog__main.c2_64_0_39_)) (= Verilog__main.tmp_stageOne_64_1_39_ Verilog__main.stageOne_64_0_39_) (= Verilog__main.tmp_stageTwo_64_1_39_ Verilog__main.stageTwo_64_0_39_)) (and (= Verilog__main.dataOut_64_2_39_ (ite (not Verilog__main.reset_64_1_39_) (bvadd Verilog__main.stageTwo_64_1_39_ Verilog__main.stageOne_64_1_39_) (_ bv0 32))) (= Verilog__main.stageOne_64_2_39_ (bvadd Verilog__main.dataIn_64_1_39_ Verilog__main.c1_64_1_39_)) (= Verilog__main.stageTwo_64_2_39_ (bvand Verilog__main.stageOne_64_1_39_ Verilog__main.c2_64_1_39_)) (= Verilog__main.tmp_stageOne_64_2_39_ Verilog__main.stageOne_64_1_39_) (= Verilog__main.tmp_stageTwo_64_2_39_ Verilog__main.stageTwo_64_1_39_)) (and (= Verilog__main.dataOut_64_3_39_ (ite (not Verilog__main.reset_64_2_39_) (bvadd Verilog__main.stageTwo_64_2_39_ Verilog__main.stageOne_64_2_39_) (_ bv0 32))) (= Verilog__main.stageOne_64_3_39_ (bvadd Verilog__main.dataIn_64_2_39_ Verilog__main.c1_64_2_39_)) (= Verilog__main.stageTwo_64_3_39_ (bvand Verilog__main.stageOne_64_2_39_ Verilog__main.c2_64_2_39_)) (= Verilog__main.tmp_stageOne_64_3_39_ Verilog__main.stageOne_64_2_39_) (= Verilog__main.tmp_stageTwo_64_3_39_ Verilog__main.stageTwo_64_2_39_)) (and (= Verilog__main.dataOut_64_4_39_ (ite (not Verilog__main.reset_64_3_39_) (bvadd Verilog__main.stageTwo_64_3_39_ Verilog__main.stageOne_64_3_39_) (_ bv0 32))) (= Verilog__main.stageOne_64_4_39_ (bvadd Verilog__main.dataIn_64_3_39_ Verilog__main.c1_64_3_39_)) (= Verilog__main.stageTwo_64_4_39_ (bvand Verilog__main.stageOne_64_3_39_ Verilog__main.c2_64_3_39_)) (= Verilog__main.tmp_stageOne_64_4_39_ Verilog__main.stageOne_64_3_39_) (= Verilog__main.tmp_stageTwo_64_4_39_ Verilog__main.stageTwo_64_3_39_))) (or (and (= Verilog__main.dataOut_64_5 Verilog__main.dataOut_64_0_39_) (= Verilog__main.stageOne_64_5 Verilog__main.stageOne_64_0_39_) (= Verilog__main.stageTwo_64_5 Verilog__main.stageTwo_64_0_39_) (= Verilog__main.tmp_stageOne_64_5 Verilog__main.tmp_stageOne_64_0_39_) (= Verilog__main.tmp_stageTwo_64_5 Verilog__main.tmp_stageTwo_64_0_39_)) (and (= Verilog__main.dataOut_64_5 Verilog__main.dataOut_64_1_39_) (= Verilog__main.stageOne_64_5 Verilog__main.stageOne_64_1_39_) (= Verilog__main.stageTwo_64_5 Verilog__main.stageTwo_64_1_39_) (= Verilog__main.tmp_stageOne_64_5 Verilog__main.tmp_stageOne_64_1_39_) (= Verilog__main.tmp_stageTwo_64_5 Verilog__main.tmp_stageTwo_64_1_39_)) (and (= Verilog__main.dataOut_64_5 Verilog__main.dataOut_64_2_39_) (= Verilog__main.stageOne_64_5 Verilog__main.stageOne_64_2_39_) (= Verilog__main.stageTwo_64_5 Verilog__main.stageTwo_64_2_39_) (= Verilog__main.tmp_stageOne_64_5 Verilog__main.tmp_stageOne_64_2_39_) (= Verilog__main.tmp_stageTwo_64_5 Verilog__main.tmp_stageTwo_64_2_39_)) (and (= Verilog__main.dataOut_64_5 Verilog__main.dataOut_64_3_39_) (= Verilog__main.stageOne_64_5 Verilog__main.stageOne_64_3_39_) (= Verilog__main.stageTwo_64_5 Verilog__main.stageTwo_64_3_39_) (= Verilog__main.tmp_stageOne_64_5 Verilog__main.tmp_stageOne_64_3_39_) (= Verilog__main.tmp_stageTwo_64_5 Verilog__main.tmp_stageTwo_64_3_39_)) (and (= Verilog__main.dataOut_64_5 Verilog__main.dataOut_64_4_39_) (= Verilog__main.stageOne_64_5 Verilog__main.stageOne_64_4_39_) (= Verilog__main.stageTwo_64_5 Verilog__main.stageTwo_64_4_39_) (= Verilog__main.tmp_stageOne_64_5 Verilog__main.tmp_stageOne_64_4_39_) (= Verilog__main.tmp_stageTwo_64_5 Verilog__main.tmp_stageTwo_64_4_39_))))) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))
(check-sat)
(exit)
