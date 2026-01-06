(set-logic QF_LIA)
(declare-fun time () Int)
(assert (and (>= time 8) (<= time 17) (distinct time 12)))
(check-sat-assuming ((= time 11)))
; Result: sat
