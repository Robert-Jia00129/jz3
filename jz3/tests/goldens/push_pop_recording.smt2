(set-logic QF_LIA)
; benchmark generated from python API
(set-info :status unknown)
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
