; EXPECT: unsat
(set-logic ALL)
(set-option :incremental false)
(declare-fun a0 () Bool)
(declare-fun a1 () Bool)
(declare-fun a2 () Bool)
(declare-fun a3 () Bool)
(declare-fun a4 () Bool)
(declare-fun a5 () Bool)
(declare-fun a6 () Bool)
(declare-fun a7 () Bool)
(declare-fun a8 () Bool)
(declare-fun a9 () Bool)
(assert a5)
(check-sat-assuming ( (not (or a0 (or a1 (or a2 (or a3 (or a4 (or a5 (or false (or a6 (or a7 (or a8 a9))))))))))) ))
