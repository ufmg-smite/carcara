; EXPECT: unsat
(set-logic ALL)

(declare-fun x () (_ BitVec 8))

(assert
  (and
    (= 2 (+ 1 1))
    (not
      (=
        (concat ((_ extract 0 0) x) ((_ extract 7 2) x) ((_ extract 1 1) x) ((_ extract 0 0) x))
        (concat ((_ extract 0 0) x) ((_ extract 7 1) x) ((_ extract 0 0) x))))))

(check-sat)
