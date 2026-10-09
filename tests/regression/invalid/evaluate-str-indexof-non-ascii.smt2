(set-logic ALL)
(assert (not (= (str.indexof "\u{e9}t\u{e9}" "t" 0) 2)))
