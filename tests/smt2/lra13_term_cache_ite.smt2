(set-logic QF_LRA)
(declare-fun b () Bool)
(declare-fun x () Real)
(assert
  (let ((?t (ite b 1 2)))
    (= (+ ?t x) (+ ?t x))))
(check-sat)
