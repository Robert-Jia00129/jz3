(set-logic QF_BV)
(set-info :status unsat)
(declare-const v0 (_ BitVec 16))
(declare-const v1 (_ BitVec 16))
(assert (= #b1 (bvnot (ite (= (ite (= (_ bv103 32) (concat v0 v1)) #b1 #b0) (bvand (ite (= v0 ((_ extract 31 16) (_ bv103 32))) #b1 #b0) (ite (= v1 ((_ extract 15 0) (_ bv103 32))) #b1 #b0))) #b1 #b0))))
(check-sat)
