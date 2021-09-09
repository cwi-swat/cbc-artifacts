(declare-const x Int)
(declare-const y Int)
(declare-const z Int)

(assert (= (- (+ (* (* 5 (* x x)) y) (* 6 (* z z z))) 7) 0))

(check-sat)
(get-model)