(set-logic ALL)
(assert ((_ tuple.select 1) (tuple 1 true)))
(assert (not ((_ tuple.select 1) (tuple 1 true))))
