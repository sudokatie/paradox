; Bitvector example
; Find an 8-bit value x such that x + 1 = 0 (overflow to find 255)
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(assert (= (bvadd x #x01) #x00))
(check-sat)
(get-model)
; Expected: sat with x = 0xFF (255)
