(declare-sort State)

(declare-fun balance (State) Int)
(declare-fun amount (State) Int)
(declare-fun step (State) Int)

(define-fun withdraw ((current State) (next State)) Bool
  (and 
    (> (amount next) 0) (< (amount next) 50)
    (> (- (balance current) (amount next)) 0)
    (= (balance next) (- (balance current) (amount next)))
    (= (step next) 1)
  )    
) 

(define-fun deposit ((current State) (next State)) Bool
  (and 
    (> (amount next) 0) (< (amount next) 50)
    (= (balance next) (+ (balance current) (amount next)))
    (= (step next) 2)
  )    
) 

(define-fun transition ((current State) (next State)) Bool
  (or 
    (deposit current next) 
    (withdraw current next)
  ) 
)

(define-fun initial ((state State)) Bool
  (and
    (= (balance state) 0)
    (= (amount state) 0)
    (= (step state) 0)
  )  
)

(define-fun goal ((state State)) Bool
  (> (balance state) 500) 
)

;(assert (forall ((s1 State) (s2 State) (s3 State)) (=> (and (deposit s1 s2) (withdraw s2 s3)) (and (withdraw s1 s2) (deposit s2 s3))))) 

(declare-const s1 State)
(declare-const s2 State)
(declare-const s3 State)

(assert
  (and
    (initial s1)
    (or
      (goal s1)
      (and (transition s1 s2) (goal s2))
      (and (transition s1 s2) (transition s2 s3) (goal s3))
    )
  )
)

(check-sat)

(get-value ((balance s1) (goal s1) (step s2) (balance s2) (amount s2) (goal s2) (step s3) (balance s3) (amount s3) (goal s3)))
  