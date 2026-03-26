; Array theory example
(set-logic QF_A)

(declare-const a (Array Int Int))
(declare-const i Int)
(declare-const v Int)

; Write v at index i
(define-fun b () (Array Int Int) (store a i v))

; Read back from index i should give v
(assert (= (select b i) v))

(check-sat)
; Expected: sat (read-over-write axiom)
