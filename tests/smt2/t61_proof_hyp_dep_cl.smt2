; Regression: proof_fail_000469 — grind failed on standalone theory clause
; "theorem cl_4: decide(c3=c0) ∨ ¬(decide(c1=c0))" because grind cannot see
; global axiom declarations.  Fixed by emitting cl_k as standalone theorems that
; load only the specific needed hypothesis (judicious context loading).
; Note: (assert (not (= c3 c3))) removed — in the unified NodeId IR,
; mk_eq(c3,c3)==mk_true() so its negation is mk_false(), detected at preprocessing
; with no EUF theory clauses.  The problem is still unsat via EUF transitivity.
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun c0 () U)
(declare-fun c1 () U)
(declare-fun c2 () U)
(declare-fun c3 () U)
(declare-fun p0 () Bool)
(declare-fun p1 () Bool)
(declare-fun f0 (U) U)
(declare-fun f1 (U) U)
(declare-fun g0 (U U) U)
(declare-fun t0 (U U U) U)
(declare-fun t1 (U U U) U)
(declare-fun b0 (Bool) U)
(declare-fun b1 (Bool) U)
(declare-fun h0 (U) Bool)
(declare-fun h1 (U U) Bool)
(declare-fun h2 (U U) Bool)
(assert (distinct (ite (distinct c1 c3) c3 c2) c0 (g0 c0 c0)))
(assert (not (= c1 (f0 c0))))
(assert (= c3 c0))
(assert (= (t1 c3 c0 (g0 c3 c0)) c3))
(assert (not (distinct c1 c2)))
(assert (not (= (ite (= (= c1 c0) (= c0 c1)) c3 c1) (f0 c2))))
(assert (not (= (f0 c3) (f0 c1))))
(assert (= c1 (g0 c2 c0)))
(assert (= c1 c0))
(check-sat)
