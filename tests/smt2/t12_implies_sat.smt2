; (=> a=b b=a) is trivially true (symmetry).  No disequality asserted => sat.
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(assert (=> (= a b) (= b a)))
(check-sat)
