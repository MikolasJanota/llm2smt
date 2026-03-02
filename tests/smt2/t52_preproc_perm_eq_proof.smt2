; Regression: --proof with --preprocess-passes 1 must not emit __flat_N proxy
; node names in bridge lemmas.  The preprocessor forces both (= a b) and
; (= (f a) c) as permanent equalities, so the theory needs to bridge atoms
; using one representative to the other.  Bridge lemmas must render as
; user-visible names like (f a) and (f b), not as internal __flat_N constants.
; Expected: unsat, proof file contains "perm_bridge" but no "__flat_".
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun c () U)
(declare-fun f (U) U)
(assert (= a b))
(assert (= (f a) c))
(assert (not (= (f b) c)))
(check-sat)
