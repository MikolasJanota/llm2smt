; Regression: ite branch atoms (e.g. (ite = then_branch)) in hypothesis
; formulas were excluded from ite_bridge emission because then/else were in
; non_shortcut.  This caused bv_decide to treat decide(branch = ite_inline)
; as an opaque atom independent of decide(branch = proxy), allowing spurious
; counterexamples.
;
; Pattern: q ↔ (n1 = ite(c, n1, n0)).  When q=true and c=false,
; ite(c,n1,n0)=n0, so n1=n0 — contradiction with n0≠n1.
; The Lean proof requires bridges for the then-branch atom (ite, n1)
; so bv_decide can connect decide(n1 = ite_inline) to decide(n1 = proxy).
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun n0 () U)
(declare-fun n1 () U)
(declare-fun p () U)
(declare-fun c () Bool)
(declare-fun q () Bool)
(assert (not (= n0 n1)))
(assert (= p (ite c n1 n0)))
(assert (= q (= n1 (ite c n1 n0))))
(assert q)
(assert (not c))
(check-sat)
; expected: unsat
