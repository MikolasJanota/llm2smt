; ite(true, P, Q) equals P.  Asserting ite(true, a=b, not(a=b)) plus not(a=b) is unsat.
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(assert (ite true (= a b) (not (= a b))))
(assert (not (= a b)))
(check-sat)
