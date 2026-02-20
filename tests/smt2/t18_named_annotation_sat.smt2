; Regression: nested (! ...) annotations, satisfiable case.
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(assert (! (not (= a b)) :named h1))
(check-sat)
; expected: sat
