(set-logic QF_LRA)
(declare-fun x () Real)
(assert
  (and true
       (or false (= (+ x 0) x))
       (=> false (< x 0))
       (= true (<= (+ x 1) (+ 1 x)))))
(check-sat)
