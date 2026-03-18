; NOT(AND(eq1,...,eqN)) is encoded as one N-literal clause, not via Tseitin
; variables for each intermediate AND node.
; This test verifies correctness of the encode_fml NOT(AND) optimisation.
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun c () U)
(declare-fun d () U)
(declare-fun e () U)
; Conjunction of distinct-value assertions (fully satisfiable).
; NOT(AND(a=b, b=c, c=d)) means we need NOT all three to hold simultaneously.
; Together with the individual assertions below the formula is UNSAT:
;   (= a b), (= b c), (= c d), (= a d)  →  all four equal
;   NOT(AND(= a b, = b c, = c d))        →  not all three hold → contradiction
(assert (= a b))
(assert (= b c))
(assert (= c d))
(assert (not (and (and (= a b) (= b c)) (= c d))))
(check-sat)
