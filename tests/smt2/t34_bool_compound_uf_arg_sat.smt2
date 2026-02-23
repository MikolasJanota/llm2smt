; t34: Regression: compound Bool expression (or) used as UF argument — sat case.
; p is true, so (or p q) is true; assert wrap(or p q) = wrap(true) is satisfiable.
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun p () Bool)
(declare-fun q () Bool)
(declare-fun wrap (Bool) U)
(assert p)
(assert (= (wrap (or p q)) (wrap true)))
(check-sat)
