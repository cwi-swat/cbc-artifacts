(set-logic HORN)

(declare-fun inv (Int) Bool)

(assert (inv 0))

(assert (forall ((I Int)) (or (> I 10) (not (inv I)) (inv (+ I 1)))))
(assert (forall ((I Int)) (=> (inv I) (<= I 11))))

(check-sat)
(get-model)

(eval (forall ((i Int)) (inv i)))