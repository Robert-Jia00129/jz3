(set-logic QF_BV)
(set-info :status unsat)
(declare-const v0 (_ BitVec 8))
(declare-const v1 (_ BitVec 8))
(declare-const v2 (_ BitVec 8))
(assert (= #b1 (ite (= (bvnot (_ bv0 8)) (bvand (bvand v0 v1) (bvand (bvnot v1) v2))) #b1 #b0)))
(check-sat)
