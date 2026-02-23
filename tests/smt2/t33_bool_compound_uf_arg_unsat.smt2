; t33: Regression: compound Bool expression (and/or/not) used as UF argument.
; (and p (not p)) is always false; wrap(false) ≠ wrap(true) is asserted;
; asserting wrap(and p (not p)) = wrap(true) forces wrap(false) = wrap(true) → unsat.
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun p () Bool)
(declare-fun wrap (Bool) U)
(declare-fun t () U)
(declare-fun f () U)
(assert (not (= t f)))
(assert (= (wrap true) t))
(assert (= (wrap false) f))
(assert (= (wrap (and p (not p))) t))
(check-sat)
