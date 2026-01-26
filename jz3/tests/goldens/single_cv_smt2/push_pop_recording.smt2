(set-logic QF_LIA)
(declare-fun x () Int)
(assert (>= x 0))
(check-sat)
; Result: sat
(push 1)
(assert (< x 0))
(check-sat)
; Result: unsat
(pop 1)
(check-sat)
; Result: sat
