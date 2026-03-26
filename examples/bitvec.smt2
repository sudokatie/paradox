; Bitvector example
(set-logic QF_BV)

(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))

; x = 0xFF
(assert (= x #xFF))

; y = x AND 0x0F
(assert (= y (bvand x #x0F)))

; Therefore y should be 0x0F
(assert (= y #x0F))

(check-sat)
; Expected: sat
