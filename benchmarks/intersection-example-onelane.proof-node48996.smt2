(set-info :smt-lib-version 2.6)
(set-logic BV)
(set-info :source |
These benchmarks used in the paper:

  Dejan Jovanovic and Leonardo de Moura.  Solving Non-Linear Arithmetic.
  In IJCAR 2012, published as LNCS volume 7364, pp. 339--354.

The keymaera family contains VCs from Keymaera verification, see:

  A. Platzer, J.-D. Quesel, and P. Rummer.  Real world verification.
  In CADE 2009, pages 485-501. Springer, 2009.

Submitted by Dejan Jovanovic for SMT-LIB.

 KeYmaera example: intersection-example-onelane.proof, node 48996 For more info see: @see "Sarah M. Loos and Andre Platzer. Safe intersections: At the crossing of hybrid systems and verification. In Kyongsu Yi, editor, 14th International IEEE Conference on Intelligent Transportation Systems, ITSC 2011, Washington, DC, USA, Proceedings. 2011."

Translated to BV by Mathias Preiner.
|)
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun v () (_ BitVec 32))
(declare-fun xI () (_ BitVec 32))
(declare-fun V () (_ BitVec 32))
(declare-fun A () (_ BitVec 32))
(declare-fun T () (_ BitVec 32))
(declare-fun B () (_ BitVec 32))
(declare-fun ep () (_ BitVec 32))
(declare-fun I1 () (_ BitVec 32))
(declare-fun X () (_ BitVec 32))
(declare-fun C () (_ BitVec 32))
(declare-fun x () (_ BitVec 32))
(declare-fun W () (_ BitVec 32))
(assert (not (exists ((T (_ BitVec 32))) (let ((?v_0 (bvadd (bvmul A T) W)) (?v_1 (bvmul (_ bv2 32) B))) (=> (and (and (and (and (and (and (and (and (and (and (and (and (and (=> (and (bvsle (_ bv0 32) T) (bvsle T C)) (and (and (bvsge ?v_0 (_ bv0 32)) (bvsle ?v_0 V)) (bvsle T ep))) (bvsge C (_ bv0 32))) (= xI X)) (bvsge W (_ bv0 32))) (bvsle W V)) (bvsgt xI (bvadd X (bvsdiv (bvmul W W) ?v_1)))) (= I1 (_ bv2 32))) (bvsgt xI (bvadd x (bvsdiv (bvmul v v) ?v_1)))) (bvsgt B (_ bv0 32))) (bvsge v (_ bv0 32))) (bvsle v V)) (bvsge A (_ bv0 32))) (bvsgt V (_ bv0 32))) (bvsgt ep (_ bv0 32))) (bvsge (bvadd (bvmul A C) W) (_ bv0 32)))))))
(check-sat)
(exit)
