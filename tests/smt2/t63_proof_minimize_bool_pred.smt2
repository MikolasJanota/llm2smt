; Regression: Bool-sorted predicate atoms in theory clauses were emitted as
; decide(True = (h a)) instead of decide((h a)), causing bv_decide to treat
; them as distinct opaque atoms and fail when --proof-minimize was used.
; (The minimizer strips most clauses, leaving only the mismatched Bool atoms.)
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun h (U) Bool)
(declare-fun a () U)
(declare-fun b () U)
(assert (= a b))
(assert (h a))
(assert (not (h b)))
(check-sat)
; expected: unsat
