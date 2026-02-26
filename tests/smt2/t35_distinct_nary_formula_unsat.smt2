; t35: Regression: distinct with 3 args used inside a compound formula (eval_lit path).
; (distinct a b c) inside (and ...) must be Tseitin-encoded, not just dispatched
; to the binary-only fast path.
; Here a=b is forced, so (distinct a b c) is false, making (and (distinct a b c) p) false.
; The only assertion is (assert (and (distinct a b c) p)) with a=b — unsat.
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun c () U)
(declare-fun p () Bool)
(assert (= a b))
(assert (and (distinct a b c) p))
(check-sat)
