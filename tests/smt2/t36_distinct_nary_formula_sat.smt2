; t36: Regression: distinct with 3 args in formula position — satisfiable case.
; All three constants can be distinct; (or (distinct a b c) p) is trivially satisfiable.
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun c () U)
(declare-fun p () Bool)
(assert (or (distinct a b c) p))
(check-sat)
