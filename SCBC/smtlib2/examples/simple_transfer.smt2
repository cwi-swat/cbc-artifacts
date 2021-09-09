(declare-sort State)
(declare-fun balance1 (State) Int)
(declare-fun balance2 (State) Int)
(declare-fun amount (State) Int)

(define-fun from1To2 ((current State) (next State)) Bool
  (and
    (>= (balance1 current) (amount next)) ; guard
    
    
    (= (- (balance1 current) (amount next)) (balance1 next))
    (= (+ (balance2 current) (amount next)) (balance2 next))
    (> (amount next) 0)
  )    
) 
(define-fun from2To1 ((current State) (next State)) Bool
  (and
    (>= (balance2 current) (amount next)) ; guard
        
    (= (+ (balance1 current) (amount next)) (balance1 next))
    (= (- (balance2 current) (amount next)) (balance2 next))
    (> (amount next) 0)
  )    
) 
(define-fun transition ((current State) (next State)) Bool
  (or 
    (from1To2 current next) 
    (from2To1 current next)
  ) 
)
(define-fun initial ((state State)) Bool
  (and
    (= (balance1 state) 100)
    (= (balance2 state) 100)
    ;(> (amount state) 0)
  )  
)
(define-fun goal ((state State)) Bool
  (> (balance1 state) 200) 
)

(declare-const S0 State)
(declare-const S1 State)
(declare-const S2 State)
(declare-const S3 State)
(declare-const S4 State)
(declare-const S5 State)
(declare-const S6 State)
(declare-const S7 State)
(declare-const S8 State)
(declare-const S9 State)
(declare-const S10 State)
(declare-const S11 State)
(declare-const S12 State)
(declare-const S13 State)
(declare-const S14 State)
(declare-const S15 State)
(declare-const S16 State)
(declare-const S17 State)
(declare-const S18 State)
(declare-const S19 State)

(assert 
  (and
    (initial S0)
    (or 
      (and  (transition S0 S1)  (goal S1))
      (and  (transition S0 S1)  (transition S1 S2)  (goal S2))
      (and  (transition S0 S1)  (transition S1 S2)  (transition S2 S3)  (goal S3))
      (and  (transition S0 S1)  (transition S1 S2)  (transition S2 S3)  (transition S3 S4)  (goal S4))
      (and  (transition S0 S1)  (transition S1 S2)  (transition S2 S3)  (transition S3 S4)  (transition S4 S5)  (goal S5))
      (and  (transition S0 S1)  (transition S1 S2)  (transition S2 S3)  (transition S3 S4)  (transition S4 S5)  (transition S5 S6)  (goal S6))
      (and  (transition S0 S1)  (transition S1 S2)  (transition S2 S3)  (transition S3 S4)  (transition S4 S5)  (transition S5 S6)  (transition S6 S7)  (goal S7))
      (and  (transition S0 S1)  (transition S1 S2)  (transition S2 S3)  (transition S3 S4)  (transition S4 S5)  (transition S5 S6)  (transition S6 S7)  (transition S7 S8)  (goal S8))
      (and  (transition S0 S1)  (transition S1 S2)  (transition S2 S3)  (transition S3 S4)  (transition S4 S5)  (transition S5 S6)  (transition S6 S7)  (transition S7 S8)  (transition S8 S9)  (goal S9))
      (and  (transition S0 S1)  (transition S1 S2)  (transition S2 S3)  (transition S3 S4)  (transition S4 S5)  (transition S5 S6)  (transition S6 S7)  (transition S7 S8)  (transition S8 S9)  (transition S9 S10)  (goal S10))
      (and  (transition S0 S1)  (transition S1 S2)  (transition S2 S3)  (transition S3 S4)  (transition S4 S5)  (transition S5 S6)  (transition S6 S7)  (transition S7 S8)  (transition S8 S9)  (transition S9 S10)  (transition S10 S11)  (goal S11))
      (and  (transition S0 S1)  (transition S1 S2)  (transition S2 S3)  (transition S3 S4)  (transition S4 S5)  (transition S5 S6)  (transition S6 S7)  (transition S7 S8)  (transition S8 S9)  (transition S9 S10)  (transition S10 S11)  (transition S11 S12)  (goal S12))
      (and  (transition S0 S1)  (transition S1 S2)  (transition S2 S3)  (transition S3 S4)  (transition S4 S5)  (transition S5 S6)  (transition S6 S7)  (transition S7 S8)  (transition S8 S9)  (transition S9 S10)  (transition S10 S11)  (transition S11 S12)  (transition S12 S13)  (goal S13))
      (and  (transition S0 S1)  (transition S1 S2)  (transition S2 S3)  (transition S3 S4)  (transition S4 S5)  (transition S5 S6)  (transition S6 S7)  (transition S7 S8)  (transition S8 S9)  (transition S9 S10)  (transition S10 S11)  (transition S11 S12)  (transition S12 S13)  (transition S13 S14)  (goal S14))
      (and  (transition S0 S1)  (transition S1 S2)  (transition S2 S3)  (transition S3 S4)  (transition S4 S5)  (transition S5 S6)  (transition S6 S7)  (transition S7 S8)  (transition S8 S9)  (transition S9 S10)  (transition S10 S11)  (transition S11 S12)  (transition S12 S13)  (transition S13 S14)  (transition S14 S15)  (goal S15))
      (and  (transition S0 S1)  (transition S1 S2)  (transition S2 S3)  (transition S3 S4)  (transition S4 S5)  (transition S5 S6)  (transition S6 S7)  (transition S7 S8)  (transition S8 S9)  (transition S9 S10)  (transition S10 S11)  (transition S11 S12)  (transition S12 S13)  (transition S13 S14)  (transition S14 S15)  (transition S15 S16)  (goal S16))
      (and  (transition S0 S1)  (transition S1 S2)  (transition S2 S3)  (transition S3 S4)  (transition S4 S5)  (transition S5 S6)  (transition S6 S7)  (transition S7 S8)  (transition S8 S9)  (transition S9 S10)  (transition S10 S11)  (transition S11 S12)  (transition S12 S13)  (transition S13 S14)  (transition S14 S15)  (transition S15 S16)  (transition S16 S17)  (goal S17))
      (and  (transition S0 S1)  (transition S1 S2)  (transition S2 S3)  (transition S3 S4)  (transition S4 S5)  (transition S5 S6)  (transition S6 S7)  (transition S7 S8)  (transition S8 S9)  (transition S9 S10)  (transition S10 S11)  (transition S11 S12)  (transition S12 S13)  (transition S13 S14)  (transition S14 S15)  (transition S15 S16)  (transition S16 S17)  (transition S17 S18)  (goal S18))
      (and  (transition S0 S1)  (transition S1 S2)  (transition S2 S3)  (transition S3 S4)  (transition S4 S5)  (transition S5 S6)  (transition S6 S7)  (transition S7 S8)  (transition S8 S9)  (transition S9 S10)  (transition S10 S11)  (transition S11 S12)  (transition S12 S13)  (transition S13 S14)  (transition S14 S15)  (transition S15 S16)  (transition S16 S17)  (transition S17 S18)  (transition S18 S19)  (goal S19))
    )
  )
)

(check-sat)
(get-model)