(set-logic QF_UF)
(declare-sort U 0)
(declare-fun c1 () U)
(declare-fun c2 () U)
(declare-fun b0 (Bool) U)
; b0 takes a Bool argument; (= c1 c2) is a Bool formula used as argument
(assert (distinct (b0 (= c1 c2)) c1))
(assert (= (b0 (= c1 c2)) c1))
(check-sat)
