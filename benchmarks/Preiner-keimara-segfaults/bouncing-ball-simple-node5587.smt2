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

 KeYmaera example: bouncing-ball-simple, node 5587 For more info see: No further information available.

Translated to BV by Mathias Preiner.
|)
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :category "industrial")
(set-info :status sat)
(declare-fun v () (_ BitVec 32))
(declare-fun t1uscore0dollarskuscore1 () (_ BitVec 32))
(declare-fun vuscore2dollarskuscore1 () (_ BitVec 32))
(declare-fun huscore2dollarskuscore1 () (_ BitVec 32))
(declare-fun tuscore2dollarskuscore1 () (_ BitVec 32))
(declare-fun h () (_ BitVec 32))
(declare-fun ts1uscore1 () (_ BitVec 32))
(assert (not (exists ((ts1uscore1 (_ BitVec 32))) (=> (and (and (and (and (and (and (and (and (and (and (bvsgt (bvadd t1uscore0dollarskuscore1 tuscore2dollarskuscore1) (_ bv0 32)) (= (bvadd (bvadd huscore2dollarskuscore1 (bvmul (bvneg (_ bv5 32)) (bvmul t1uscore0dollarskuscore1 t1uscore0dollarskuscore1))) (bvmul t1uscore0dollarskuscore1 vuscore2dollarskuscore1)) (_ bv0 32))) (=> (and (bvsle (_ bv0 32) ts1uscore1) (bvsle ts1uscore1 t1uscore0dollarskuscore1)) (bvsge (bvadd (bvadd huscore2dollarskuscore1 (bvmul (bvneg (_ bv5 32)) (bvmul ts1uscore1 ts1uscore1))) (bvmul ts1uscore1 vuscore2dollarskuscore1)) (_ bv0 32)))) (bvsge t1uscore0dollarskuscore1 (_ bv0 32))) (= huscore2dollarskuscore1 (bvadd (bvmul (_ bv5 32) (bvmul tuscore2dollarskuscore1 tuscore2dollarskuscore1)) (bvmul vuscore2dollarskuscore1 tuscore2dollarskuscore1)))) (bvsge huscore2dollarskuscore1 (_ bv0 32))) (bvsge tuscore2dollarskuscore1 (_ bv0 32))) (bvsle vuscore2dollarskuscore1 (bvadd (bvmul (bvneg (_ bv10 32)) tuscore2dollarskuscore1) (_ bv16 32)))) (bvsle tuscore2dollarskuscore1 (bvsdiv (_ bv16 32) (_ bv5 32)))) (= h (_ bv0 32))) (= v (_ bv16 32))) (bvsle (bvsdiv (bvneg (bvadd (bvmul (bvneg (_ bv10 32)) t1uscore0dollarskuscore1) vuscore2dollarskuscore1)) (_ bv2 32)) (_ bv16 32))))))
(check-sat)
(exit)
