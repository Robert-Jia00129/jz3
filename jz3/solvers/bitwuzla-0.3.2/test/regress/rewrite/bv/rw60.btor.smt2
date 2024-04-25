(set-logic QF_BV)
(set-info :status unsat)
(declare-const v0 (_ BitVec 32))
(declare-const v1 (_ BitVec 32))
(declare-const v2 (_ BitVec 32))
(declare-const v3 (_ BitVec 32))
(assert (= #b1 (bvnot (ite (= (bvmul (bvadd (bvadd (bvadd v0 v1) v2) v3) (bvadd (bvadd v0 v3) (bvadd v1 v2))) (bvmul (bvadd (bvadd v0 v3) (bvadd v1 v2)) (bvadd (bvadd v0 v3) (bvadd v1 v2)))) #b1 #b0))))
(check-sat)
