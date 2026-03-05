(set-logic QF_UF)
(declare-sort U 0)
(declare-fun c0 () U)
(declare-fun c1 () U)
(declare-fun c2 () U)
(declare-fun c3 () U)
(declare-fun p1 () Bool)
(declare-fun f0 (U) U)
(declare-fun b1 (Bool) U)
(declare-fun h0 (U U) Bool)
; Regression: proof_fail_000064 — SAT assigns equalities before EUF can
; propagate them (already_assigned atoms).  The CC explanation for such atoms
; includes the self-referential SAT edge, which must be skipped to avoid
; tautological reason clauses.  Trivial unit reason clauses with no permanent
; equality premises must not be emitted (grind cannot prove them in isolation).
(assert (= c0 c1 c3))
(assert (= c1 (b1 p1)))
(assert (not (= (f0 c3) (f0 c1))))
(assert (= c3 (b1 (h0 c2 c0))))
(check-sat)
