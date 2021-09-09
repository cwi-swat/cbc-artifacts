(declare-const a Bool)
(declare-const b Bool)
(declare-const c Bool)
(declare-const d Bool)


(define-fun law1 () Bool 
  (= (or (and a b) (and c d)) (and (or a c) (or b d))))

(define-fun law2 () Bool 
  (= (or (and a b) (and a c)) (and a (or b c))))


(assert (not law2))

(check-sat)
(get-model)