; Linear Integer Arithmetic example
; Find x,y such that x + y = 10 and x - y = 4
(set-logic QF_LIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= (+ x y) 10))
(assert (= (- x y) 4))
(check-sat)
(get-model)
; Expected: sat with x=7, y=3
