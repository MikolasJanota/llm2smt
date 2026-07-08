; Simple same-variable bounds expose SAT-visible unate implications.
(set-logic QF_LRA)
(declare-fun x () Real)
(declare-fun p () Bool)
(assert (or p (<= x 1) (<= x 2) (< x 2) (>= x 0) (> x (- 1))))
(check-sat)
