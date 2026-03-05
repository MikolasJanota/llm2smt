(set-logic QF_UF)
(declare-sort U 0)
(declare-fun p (U U) Bool)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun c () U)
; The simplifier forces a=b permanent (direct positive-equality assertion).
; Conflict: p(a,c) AND ¬p(b,c) together with a=b gives a non-unit EUF conflict
; whose clause needs a=b as a premise (permanent eq, no SAT literal).
(assert (= a b))
(assert (p a c))
(assert (not (p b c)))
(check-sat)
