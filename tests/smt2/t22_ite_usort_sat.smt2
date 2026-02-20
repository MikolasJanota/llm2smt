; Regression: U-sorted ite, satisfiable case.
; x = (ite c a b), c is true → x = a is forced; consistent with x ≠ b.
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun c () Bool)
(declare-fun x () U)
(assert (not (= a b)))
(assert c)
(assert (= x (ite c a b)))
(assert (= x a))
(check-sat)
; expected: sat
