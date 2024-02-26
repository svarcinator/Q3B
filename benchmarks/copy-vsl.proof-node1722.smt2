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

 KeYmaera example: vsl.proof, node 1722 For more info see: No further information available.

Translated to BV by Mathias Preiner.
|)
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun A () (_ BitVec 32))
(declare-fun vsluscore6dollarskuscore2 () (_ BitVec 32))
(declare-fun v1uscore3dollarskuscore2 () (_ BitVec 32))
(declare-fun B () (_ BitVec 32))
(declare-fun ep () (_ BitVec 32))
(declare-fun x1uscore3dollarskuscore1 () (_ BitVec 32))
(declare-fun vsluscore8dollarskuscore0 () (_ BitVec 32))
(declare-fun ts1uscore0 () (_ BitVec 32))
(declare-fun t8uscore0dollarskuscore0 () (_ BitVec 32))
(declare-fun xsluscore8dollarskuscore0 () (_ BitVec 32))
(assert (not (exists ((ts1uscore0 (_ BitVec 32))) (let ((?v_0 (bvneg B))) (=> (and (and (and (and (and (and (and (and (and (=> (and (bvsle (_ bv0 32) ts1uscore0) (bvsle ts1uscore0 t8uscore0dollarskuscore0)) (and (bvsge (bvadd (bvmul ?v_0 ts1uscore0) v1uscore3dollarskuscore2) (_ bv0 32)) (bvsle ts1uscore0 ep))) ) ) (bvsge xsluscore8dollarskuscore0 (bvadd (bvadd x1uscore3dollarskuscore1 (bvsdiv (bvsub (bvmul v1uscore3dollarskuscore2 v1uscore3dollarskuscore2) (bvmul vsluscore8dollarskuscore0 vsluscore8dollarskuscore0)) (bvmul (_ bv2 32) B))) (bvmul (bvadd (bvsdiv A B) (_ bv1 32)) (bvadd (bvmul (bvsdiv A (_ bv2 32)) (bvmul ep ep)) (bvmul ep v1uscore3dollarskuscore2)))))) ) ) (bvsle v1uscore3dollarskuscore2 vsluscore6dollarskuscore2)) ) ) ) (bvsge (bvadd (bvmul ?v_0 t8uscore0dollarskuscore0) v1uscore3dollarskuscore2) (_ bv0 32)))))))
(check-sat)
(get-model)
(exit)
