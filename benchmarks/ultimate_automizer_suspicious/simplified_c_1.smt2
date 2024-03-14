(set-info :smt-lib-version 2.6)
(set-logic BV)
(set-info :source |
Generated by the tool Ultimate Automizer [1,2] which implements
an automata theoretic approach [3] to software verification.

This SMT script belongs to a set of SMT scripts that was generated by
applying Ultimate Automizer to benchmarks [4] from the SV-COMP 2023 [5,6].
This script may not contain all SMT commands that Ultimate Automizer
issued. In order to meet the restrictions for SMT-COMP benchmarks 
we dropped the commands for getting values (resp. models), 
unsatisfiable cores, and interpolants.

2023-03-21, Matthias Heizmann (heizmann@informatik.uni-freiburg.de)

[1] https://ultimate.informatik.uni-freiburg.de/automizer/
[2] Matthias Heizmann, Max Barth, Daniel Dietsch, Leonard Fichtner,
     Jochen Hoenicke, Dominik Klumpp, Mehdi Naouar, Tanja Schindler,
     Frank Schüssele, Andreas Podelski: Ultimate Automizer and the
     CommuHash Normal Form (Competition Contribution). TACAS 2023
[3] Matthias Heizmann, Jochen Hoenicke, Andreas Podelski: Software Model
     Checking for People Who Love Automata. CAV 2013
[4] https://github.com/sosy-lab/sv-benchmarks
[5] Dirk Beyer: Competition on Software Verification and
     Witness Validation: SV-COMP 2023.  TACAS 2023
[6] https://sv-comp.sosy-lab.org/2023/
|)
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :category "industrial")
(set-info :status unknown)
(declare-fun |y| () (_ BitVec 32))
(assert  (exists ((|z| (_ BitVec 32))) (= (bvor (bvand |z| (_ bv16777215 32)) (_ bv16777216 32)) |y|)) )



(assert 
(forall ((|w| (_ BitVec 32)) (|v| (_ BitVec 32)) (|x| (_ BitVec 32))) (not (= |y| (bvlshr (bvadd (bvor (bvand |x| (_ bv16777215 32)) (_ bv16777216 32)) (bvlshr (bvor (_ bv16777216 32) (bvand |w| (_ bv16777215 32))) |v|)) (_ bv1 32)))))
)
(check-sat)
(exit)

(forall ((|1| (_ BitVec 32)) (|2| (_ BitVec 32)) (|3| (_ BitVec 32)))
  (! (let ((a!1 (bvadd (concat #x01 ((_ extract 23 0) |3|))
                       (bvlshr (concat #x01 ((_ extract 23 0) |1|)) |2|))))
       (or (not (= ((_ extract 31 25) a!1) #b0000001))
           (not (= ((_ extract 23 0) |0|) ((_ extract 24 1) a!1)))))
     :weight 0))

