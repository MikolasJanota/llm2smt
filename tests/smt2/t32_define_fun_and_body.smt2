; Regression: define-fun whose body is a conjunction (and).
; The body is expanded structurally via assert_formula, not via a Tseitin proxy.
; All conjuncts must hold; together they imply unsat.
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun c () U)
(declare-fun f (U) U)
(define-fun |my conjunction| () Bool
  (and (= a b) (= b c)))
(assert |my conjunction|)
(assert (not (= (f a) (f c))))
(check-sat)
