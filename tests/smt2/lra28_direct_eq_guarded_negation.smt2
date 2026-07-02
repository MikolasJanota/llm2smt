(set-logic QF_LRA)
(declare-fun x () Real)
(assert (or (not (= x 0)) (> x 1)))
(check-sat)
