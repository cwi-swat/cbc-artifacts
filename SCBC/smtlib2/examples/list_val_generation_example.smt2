(set-option :produce-proofs true)
(set-option :produce-unsat-cores true)

(declare-fun now () Int)
(assert (= now 1424960995018))

(declare-fun inleg () Int)

(assert (= inleg 80))

(declare-fun new.balance ( Int) Int)

(define-fun balance ((input Int)) Int 
  (ite (< input 10) 100
    (ite (< input 20) 200 300)
  )
)

(assert (= (new.balance  now) inleg))

(assert (forall ( (x Int)  ) 
  (=> (< x now) (= (balance x) (new.balance x)))
))

(check-sat)
(get-model)

(assert (not (= (new.balance now) 80)))
(check-sat)