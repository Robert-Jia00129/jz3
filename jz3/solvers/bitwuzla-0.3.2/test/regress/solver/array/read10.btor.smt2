(set-logic QF_ABV)
(set-info :status unsat)
(declare-const a0 (Array (_ BitVec 1) (_ BitVec 1) ))
(declare-const v0 (_ BitVec 1))
(declare-const v1 (_ BitVec 1))
(assert (= #b1 (bvnot (bvor (bvnot (ite (= v0 v1) #b1 #b0)) (ite (= (select a0 (bvand v0 v1)) (select a0 (bvor v0 v1))) #b1 #b0)))))
(check-sat)
