(set-logic QF_BV)
(set-info :status sat)
(declare-const v0 (_ BitVec 17))
(declare-const v1 (_ BitVec 17))
(assert (= #b1 (ite (= (bvmul ((_ zero_extend 17) v0) ((_ zero_extend 17) v1)) (_ bv4294967295 34)) #b1 #b0)))
(check-sat)