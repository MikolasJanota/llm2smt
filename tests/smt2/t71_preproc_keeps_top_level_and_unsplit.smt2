(set-logic QF_UF)
(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun c () U)
(declare-fun x () U)
(assert
  (and
    (not (= a b))
    (not (= b c))
    (not (= a c))
    (or (= x a) (= x b) (= x c))))
(check-sat)
