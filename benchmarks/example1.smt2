(set-logic BV)
(declare-fun p () Bool)
(declare-fun q () Bool)
(assert (and p (not q)))
(check-sat)
(exit)
