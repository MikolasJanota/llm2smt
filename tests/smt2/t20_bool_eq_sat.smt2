; Regression: (= p p) is a tautology — satisfiable alone, and with another constraint.
; Also covers the Goel pattern: (= Bool-var (not Bool-var2)).
(set-logic QF_UF)
(declare-fun p () Bool)
(declare-fun q () Bool)
(assert (= p q))   ; p ↔ q
(assert p)         ; force p (and therefore q) true
(check-sat)
; expected: sat
