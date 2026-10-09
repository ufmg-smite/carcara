(set-logic ALL)
(declare-datatype Color ((red) (green)))
(declare-const c Color)
(assert (not (= (match c ((red true) (green false))) (match c ((red true) (green false))))))
