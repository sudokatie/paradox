; LIA (Linear Integer Arithmetic) example
(set-logic QF_LIA)

(declare-const x Int)
(declare-const y Int)

; x > 0
(assert (> x 0))

; y < 10
(assert (< y 10))

; x + y = 15
(assert (= (+ x y) 15))

; This is satisfiable: e.g., x = 6, y = 9
(check-sat)
(get-model)
