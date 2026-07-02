(set-logic QF_LRA)
(declare-fun x () Real)
(assert (= (ite true (+ x 0) (+ x 1)) x))
(check-sat)
