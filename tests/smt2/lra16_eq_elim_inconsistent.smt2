(set-logic QF_LRA)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (and
  (= (+ x y) 2)
  (= (+ (* 2 x) (* 2 y)) 5)))
(check-sat)
