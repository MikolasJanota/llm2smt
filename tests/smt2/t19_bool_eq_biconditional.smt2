; Regression: (= Bool Bool) must be treated as biconditional, not theory equality.
; (= p (not p)) is always false → unsat.
(set-logic QF_UF)
(declare-fun p () Bool)
(assert (= p (not p)))
(check-sat)
; expected: unsat
