(set-logic QF_BV)
(set-info :status unsat)
(declare-const v0 (_ BitVec 3))
(assert (= #b1 (ite (= (bvmul v0 v0) #b101) #b1 #b0)))
(check-sat)
