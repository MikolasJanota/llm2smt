; Regression: --proof with U-sorted ite must inline the ite as `(if c then a else b)`
; and add ite semantic have-clauses so sat_decide can close the proof.
; The proof for this file previously failed (sat_decide saw a spurious model).
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
