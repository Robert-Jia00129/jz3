(set-logic ALL)
(set-info :status unsat)
(declare-sort $$unsorted 0)
(declare-fun tptp.big_f ($$unsorted $$unsorted) Bool)
(assert (exists ((Z $$unsorted) (W $$unsorted)) (forall ((X $$unsorted) (Y $$unsorted)) (= (tptp.big_f X Y) (and (= X Z) (= Y W))))))
(assert (not (exists ((W $$unsorted)) (forall ((Y $$unsorted)) (= (exists ((Z $$unsorted)) (forall ((X $$unsorted)) (= (tptp.big_f X Y) (= X Z)))) (= Y W))))))
(set-info :filename SYN075+1)
(check-sat-assuming ( true ))
