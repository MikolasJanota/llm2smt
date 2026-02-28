(set-logic QF_UF)
(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun c () U)
; (= a b c) means (and (= a b) (= b c)), transitively a=c
(assert (= a b c))
(assert (not (= a c)))
(check-sat)
