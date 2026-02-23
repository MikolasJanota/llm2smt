; Regression: define-fun with quoted (space-containing) names.
; The macro |f is f| expands to an equality atom; asserting it and the
; matching disequality must yield unsat.
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(define-fun |f is f| () Bool (= a b))
(assert |f is f|)
(assert (not (= a b)))
(check-sat)
