; Regression: heap-use-after-free in Flattener::do_flatten.
;
; Flattener::do_flatten holds a `const NodeData& data = nm_.get(term)`, then
; calls nm_.mk_const(fn_sym) which may push_back into nodes_, invalidating the
; reference.  The subsequent `for (child : data.children)` loop reads freed
; memory and causes a segfault.
;
; The formula is trivially satisfiable, but triggers the UAF because
; the nested application g0(f0(c0), g0(c3, c1)) forces the flattener to call
; nm_.mk_const for g0's symbol node while holding a reference into nodes_.
;
; Expected: sat
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun c0 () U)
(declare-fun c1 () U)
(declare-fun c3 () U)
(declare-fun f0 (U) U)
(declare-fun g0 (U U) U)
(assert (= c3 (g0 (f0 c0) (g0 c3 c1))))
(check-sat)
; expected: sat
