(set-logic QF_BV)
(set-info :status sat)
(declare-const v0 (_ BitVec 4))
(assert (= #b1 (bvnot (ite (= (bvadd (bvnot v0) (bvnot #b1100)) (bvadd (bvnot v0) (bvnot #b1010))) #b1 #b0))))
(check-sat)
