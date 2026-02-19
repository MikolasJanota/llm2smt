; Asserting false directly makes the problem unsatisfiable.
(set-logic QF_UF)
(declare-sort U 0)
(assert false)
(check-sat)
