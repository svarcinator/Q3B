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

 KeYmaera example: bouncing-ball-simple, node 5919 For more info see: No further information available.

Translated to BV by Mathias Preiner.
|)
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :category "industrial")
(set-info :status unknown)
(declare-fun tuscore2dollarskuscore4 () (_ BitVec 32))
(declare-fun vuscore2dollarskuscore4 () (_ BitVec 32))
(declare-fun huscore2dollarskuscore4 () (_ BitVec 32))
(declare-fun v () (_ BitVec 32))
(declare-fun t1uscore0dollarskuscore4 () (_ BitVec 32))
(declare-fun ts1uscore4 () (_ BitVec 32))
(declare-fun h () (_ BitVec 32))
(assert (not (exists ((ts1uscore4 (_ BitVec 32))) (let ((?v_0 (bvadd t1uscore0dollarskuscore4 tuscore2dollarskuscore4))) (=> (and (and (and (and (and (and (and (and (=> (and (bvsle (_ bv0 32) ts1uscore4) (bvsle ts1uscore4 t1uscore0dollarskuscore4)) (bvsge (bvadd (bvadd huscore2dollarskuscore4 (bvmul (bvneg (_ bv5 32)) (bvmul ts1uscore4 ts1uscore4))) (bvmul ts1uscore4 vuscore2dollarskuscore4)) (_ bv0 32))) (bvsge t1uscore0dollarskuscore4 (_ bv0 32))) (= huscore2dollarskuscore4 (bvadd (bvmul (_ bv5 32) (bvmul tuscore2dollarskuscore4 tuscore2dollarskuscore4)) (bvmul vuscore2dollarskuscore4 tuscore2dollarskuscore4)))) (bvsge huscore2dollarskuscore4 (_ bv0 32))) (bvsge tuscore2dollarskuscore4 (_ bv0 32))) (bvsle vuscore2dollarskuscore4 (bvadd (bvmul (bvneg (_ bv10 32)) tuscore2dollarskuscore4) (_ bv16 32)))) (bvsle tuscore2dollarskuscore4 (bvsdiv (_ bv16 32) (_ bv5 32)))) (= h (_ bv0 32))) (= v (_ bv16 32))) (or (bvsgt ?v_0 (_ bv0 32)) (bvsge ?v_0 (_ bv0 32))))))))
(check-sat)
(exit)
