(set-option :smt.mbqi true)

(declare-fun trans (Int Int) Int)

(define-fun pre ((balance Int) (amount Int)) Bool 
  (and (>= balance amount) (> amount 0))
)

(define-fun post ((new.balance Int) (old.balance Int) (amount Int)) Bool
  (= new.balance (- old.balance amount))
)
 
;(assert (forall ((balance Int) (amount Int)) 
;  (=> (pre balance amount) (post (trans balance amount) balance amount))
;))

;(check-sat)
(get-model)