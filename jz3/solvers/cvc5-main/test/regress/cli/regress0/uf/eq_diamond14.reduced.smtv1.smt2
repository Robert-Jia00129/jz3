(set-option :incremental false)
(set-info :source "Reduced by delta debugger from eq_diamond14 to fix a UF bug.")
(set-info :status unsat)
(set-logic QF_UF)
(declare-sort U 0)
(declare-sort V 0)
(declare-fun x13 () V)
(declare-fun x0 () V)
(declare-fun y12 () V)
(declare-fun x12 () V)
(declare-fun z11 () V)
(declare-fun x11 () V)
(declare-fun y11 () V)
(declare-fun z10 () V)
(declare-fun x10 () V)
(declare-fun y10 () V)
(declare-fun y9 () V)
(declare-fun x9 () V)
(declare-fun y8 () V)
(declare-fun x8 () V)
(declare-fun y7 () V)
(declare-fun x7 () V)
(declare-fun y6 () V)
(declare-fun x6 () V)
(declare-fun y5 () V)
(declare-fun x5 () V)
(declare-fun y4 () V)
(declare-fun x4 () V)
(declare-fun y3 () V)
(declare-fun x3 () V)
(declare-fun y2 () V)
(declare-fun x2 () V)
(declare-fun y1 () V)
(declare-fun x1 () V)
(declare-fun y0 () V)
(check-sat-assuming ( (and (and (= x0 y0) (= y0 x1)) (and (= x1 y1) (= y1 x2)) (and (= x2 y2) (= y2 x3)) (and (= x3 y3) (= y3 x4)) (and (= x4 y4) (= y4 x5)) (and (= x5 y5) (= y5 x6)) (and (= x6 y6) (= y6 x7)) (and (= x7 y7) (= y7 x8)) (and (= x8 y8) (= y8 x9)) (and (= x9 y9) (= y9 x10)) (or (and false (= y10 x11)) (and (= x10 z10) (= x11 z10))) (or (and (= x11 y11) (= y11 x12)) (and (= x11 z11) (= x12 z11))) (and (= x12 y12) (= y12 x13)) (not (= x0 x13))) ))
