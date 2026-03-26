; Combined theories example (Arrays + UF + LIA)
(set-logic QF_AUFLIA)

(declare-const a (Array Int Int))
(declare-const i Int)
(declare-const j Int)
(declare-fun f (Int) Int)

; i > 0
(assert (> i 0))

; j = i + 1
(assert (= j (+ i 1)))

; Write f(i) at index i
(define-fun b () (Array Int Int) (store a i (f i)))

; Write f(j) at index j
(define-fun c () (Array Int Int) (store b j (f j)))

; Reading index i from c should still give f(i)
; (since j != i when j = i + 1 and i > 0)
(assert (= (select c i) (f i)))

(check-sat)
; Expected: sat
