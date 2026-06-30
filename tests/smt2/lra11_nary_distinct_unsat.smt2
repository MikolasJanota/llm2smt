(set-logic QF_LRA)
(declare-fun x () Real)
(assert (distinct x (+ x 0) (+ x 1)))
(check-sat)
