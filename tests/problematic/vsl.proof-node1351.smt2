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

 KeYmaera example: vsl.proof, node 1351 For more info see: No further information available.

Translated to BV by Mathias Preiner.
|)
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun ts0uscore0 () (_ BitVec 32))
(declare-fun vsluscore6dollarskuscore0 () (_ BitVec 32))
(declare-fun v1uscore3dollarskuscore0 () (_ BitVec 32))
(declare-fun A () (_ BitVec 32))
(declare-fun B () (_ BitVec 32))
(declare-fun t7uscore0dollarskuscore0 () (_ BitVec 32))
(declare-fun ep () (_ BitVec 32))
(assert (not (exists ((ts0uscore0 (_ BitVec 32))) (let ((?v_0 (bvneg B))) (=> (and (and (and (and (and (and (and (=> (and (bvsle (_ bv0 32) ts0uscore0) (bvsle ts0uscore0 t7uscore0dollarskuscore0)) (and (bvsge (bvadd (bvmul ?v_0 ts0uscore0) v1uscore3dollarskuscore0) (_ bv0 32)) (bvsle ts0uscore0 ep))) (bvsge t7uscore0dollarskuscore0 (_ bv0 32))) (bvsge v1uscore3dollarskuscore0 (_ bv0 32))) (bvsge vsluscore6dollarskuscore0 (_ bv0 32))) (bvsle v1uscore3dollarskuscore0 vsluscore6dollarskuscore0)) (bvsge A (_ bv0 32))) (bvsgt B (_ bv0 32))) (bvsgt ep (_ bv0 32))) (bvsge (bvadd (bvmul ?v_0 t7uscore0dollarskuscore0) v1uscore3dollarskuscore0) (_ bv0 32)))))))
(check-sat)
(exit)
