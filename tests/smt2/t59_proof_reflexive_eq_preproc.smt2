(set-logic QF_UF)
(declare-sort U 0)
(declare-fun c0 () U)
(declare-fun c1 () U)
; Regression: proof_fail_000006 with --preprocess-passes 1.
; The simplifier must constant-fold Eq(c0,c0) to True in Phase 1 so that
; Not(Eq(c0,c0)) becomes False immediately.  Without the fix, Not(Eq(c0,c0))
; was treated as a unit-negative atom, self-substituted to True, and the proof
; snapshot had hyp2:True (no contradiction) instead of hyp2:False.
(assert (= c0 c1))
(assert (not (= c0 c0)))
(check-sat)
