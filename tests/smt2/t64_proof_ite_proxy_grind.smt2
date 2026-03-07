; Regression: ite nodes inlined as `(if cond then a else b)` inside
; `decide(... = ...)` in theory clauses caused `grind` to fail via
; case-splitting on the ite expression.  The fix: when a proxy constant
; p is equated with an ite node (p = ite(c,a,b)), use p's name in theory
; clause atoms instead of the inlined ite expression.
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun c () Bool)
(declare-fun p () U)
(declare-fun x () U)
(assert (= p (ite c a b)))
(assert (= x p))
(assert (not (= x a)))
(assert (not (= x b)))
(check-sat)
; expected: unsat
