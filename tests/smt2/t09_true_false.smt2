; true is trivially satisfied, false is unsatisfiable.
; Asserting (and true (not false)) should be sat.
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun a () U)
(assert true)
(assert (not false))
(check-sat)
