; ite(false, a=b, true) simplifies to true — always sat.
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(assert (ite false (= a b) true))
(check-sat)
