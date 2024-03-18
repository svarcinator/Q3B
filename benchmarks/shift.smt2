(set-logic BV)
(declare-fun x () (_ BitVec 4))
(declare-fun y () (_ BitVec 4))
(assert
 (
  or (and (= (bvshl x #b0010) y) (= y #b1000))
     (bvslt x (bvand x y))
 )
)
(check-sat)
(exit)
