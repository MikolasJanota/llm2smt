(set-logic QF_UF)
(declare-sort U 0)
(declare-fun c0 () U)
(declare-fun c1 () U)
(declare-fun c2 () U)
(declare-fun c3 () U)
(declare-fun h1 (U) Bool)
; Regression: proof_fail_000052 with --preprocess-passes 1.
; The simplifier substitutes perm equalities (c0→c1, c3→c2) into Eq atoms.
; The proof snapshot must be taken AFTER simplification so the Lean proof uses
; the same atom representations as the SAT encoding.
; Without the fix, the xor formula renders Eq(c0,c2) as decide(c2=c0)
; (NodeId(c0)>NodeId(c2), so c2 comes first in canonical order) while the
; SAT encoding uses decide(c1=c2) — bv_decide treats them as different atoms.
(assert (= c0 c1))
(assert (= c3 c2))
(assert (xor (= c0 c2) (ite (xor (distinct c2 c2) (= c2 c3)) false (distinct c1 c1 c3))))
(assert (ite (ite (h1 c3) (= c1 c1) (= c3 c1)) false (= (= c1 c2 c2) (= c1 c3))))
(check-sat)
