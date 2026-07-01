(set-logic QF_LRA)
(declare-fun x () Real)
(assert (or (= x 1) (= x 2) (= x 3)))
(check-sat)
