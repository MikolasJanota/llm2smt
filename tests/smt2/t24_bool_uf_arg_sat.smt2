; Satisfiable companion to t23: Bool-sorted symbol as UF argument, no conflict.
; p is forced true, q is forced false; f(p)≠f(q) is consistent because
; p and q map to distinct EUF nodes (true_node vs false_node).
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun p () Bool)
(declare-fun q () Bool)
(declare-fun f (Bool) U)
(assert p)
(assert (not q))
(assert (not (= (f p) (f q))))
(check-sat)
; expected: sat
