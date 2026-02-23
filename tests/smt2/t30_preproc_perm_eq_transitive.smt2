; Regression: permanent equality with transitivity.
; Both (= a b) and (= b c) are forced by the preprocessor; combined they
; imply a = c, which contradicts (not (= (f a) (f c))).
; Expected: unsat.
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun c () U)
(declare-fun f (U) U)
(assert (= a b))
(assert (= b c))
(assert (not (= (f a) (f c))))
(check-sat)
