; Regression: permanent equality optimization.
; (= a b) is forced true by the preprocessor (unit clause) and should be
; committed directly into the CC as a permanent merge (no SAT variable).
; The disequality (not (= (f a) (f b))) contradicts it via congruence.
; Expected: unsat.
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun f (U) U)
(assert (= a b))
(assert (not (= (f a) (f b))))
(check-sat)
