; EUF (Equality with Uninterpreted Functions) example
(set-logic QF_UF)

(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun c () U)
(declare-fun f (U) U)

; Assert a = b
(assert (= a b))

; Assert f(a) != f(b) - this should be UNSAT due to congruence
; (assert (not (= (f a) (f b))))

; Instead, assert something satisfiable:
; a = b AND f(a) = c
(assert (= (f a) c))

(check-sat)
; Expected: sat
