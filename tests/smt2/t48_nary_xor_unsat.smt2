(set-logic QF_UF)
(declare-fun p () Bool)
(declare-fun q () Bool)
(declare-fun r () Bool)
; (xor p q r) = (xor (xor p q) r), asserted true
; also assert p, q, r — so (xor p q) = xor(T,T) = F, then xor(F, r=T) = T... wait
; let's make it unsat: p=T, q=T, r=F -> xor(xor(T,T),F)=xor(F,F)=F, contradiction
(assert (xor p q r))
(assert p)
(assert q)
(assert (not r))
(check-sat)
