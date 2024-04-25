(set-option :incremental false)
(set-info :status unsat)
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun x () U)
(declare-fun y () U)
(declare-fun z () U)
(check-sat-assuming ( (not (= (distinct x y z) (and (not (= x y)) (not (= x z)) (not (= y z))))) ))
