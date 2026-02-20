; Regression: U-sorted ite  (ite cond U-term U-term)  must be encoded as a
; fresh EUF constant with conditional equalities, not treated as a Bool ite.
; Here: x = (ite c a b), x ≠ a, x ≠ b  forces c to be both true and false → unsat.
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun c () Bool)
(declare-fun x () U)
(assert (= x (ite c a b)))
(assert (not (= x a)))
(assert (not (= x b)))
(check-sat)
; expected: unsat
