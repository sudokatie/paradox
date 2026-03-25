; Array theory example
; Read-over-write: prove that a[i := v][i] = v
(set-logic QF_AX)
(declare-fun a () (Array Int Int))
(declare-fun i () Int)
(declare-fun v () Int)
(assert (not (= (select (store a i v) i) v)))
(check-sat)
; Expected: unsat (read-over-write axiom)
