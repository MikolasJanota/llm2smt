; xor(P, not P) is always true, so the problem is sat.
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(assert (xor (= a b) (not (= a b))))
(check-sat)
