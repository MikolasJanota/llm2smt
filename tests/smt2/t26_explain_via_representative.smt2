; Regression: incomplete proof-forest explanation when the pending-entry node in
; the merged class differs from the class representative (EqId-reuse after backtrack).
;
; Setup: a, b, mid, extra are U-sorted constants.
;   (a ≠ b) — permanent disequality.
;   The ite encoding makes (a = mid) and (b = mid) conditionally assertable.
;   Both conditions can be true simultaneously (they are free Bools), which
;   would make a ≡ mid ≡ b — conflicting with a ≠ b.
;
; Bug (before fix): when repr[mid] = b (because b=mid was asserted first at a
; lower decision level), processing (a = mid) would create a proof edge from
; b's representative to a, labeled only with the (a=mid) equation.
; The generated conflict clause for a ≠ b then omitted (b=mid), making the
; conflict clause too weak — it incorrectly forced NOT(a=mid) as a unit, even
; though the formula is SAT (just choose (a=mid) false and (b=mid) false).
;
; Fix: the proof edge now stores from_node=mid; explain adds (b,mid) to the
; worklist, returning both (a=mid) and (b=mid) in the conflict clause.
;
; Expected: sat  (choose both a≠mid and b≠mid, preserving a≠b)
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun a   () U)
(declare-fun b   () U)
(declare-fun mid () U)
(declare-fun p () Bool)
(declare-fun q () Bool)
; a ≠ b is the permanent disequality.
(assert (not (= a b)))
; Two optional equalities (ite-encoded): p → a=mid, q → b=mid.
; Neither is forced; both being true would conflict (a≡b), but the SAT solver
; should backtrack and find the model where both are false.
(assert (= a (ite p mid a)))
(assert (= b (ite q mid b)))
(check-sat)
; expected: sat  (p=false, q=false → a≠mid, b≠mid, a≠b holds)
