; Regression: (! term :named label) annotation syntax must be stripped and the
; inner term processed normally.  Both assert and check-sat path must work.
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(assert (! (= a b) :named hyp1))
(assert (! (not (= a b)) :named goal))
(check-sat)
; expected: unsat
