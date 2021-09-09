(declare-sort State)

(define-fun initial ((st State)) Bool
  (and (= (counter st) 0) (not (= st nil)))
)

(define-fun transitionCondition ((cur State) (nex State)) Bool
  (or
    (= (counter nex) (+ (counter cur) 1))
    false;(= (counter nex) (- (counter cur) 1))
  )
) 

(define-fun errorCondition ((st State)) Bool
  (= (counter st) (- 10))
)

;(push 1)
;
;(assert 
;	(exists ((s1 State) (s2 State))
;		(and
;			(not (errorCondition s1))
;			(transitionCondition s1 s2)
;			(errorCondition s2)
;		)
;	)
;)
;
;(check-sat) 
;
;(pop 1)

(declare-const S0 State)
(declare-const S1 State)
(declare-const S2 State)
(declare-const S3 State)
;(declare-const S4 State)
;(declare-const S5 State)
;(declare-const S6 State)
;(declare-const S7 State)
;(declare-const S8 State)
;(declare-const S9 State)
;(declare-const S10 State)
;(declare-const S11 State)

(declare-fun reachable (State State) Bool)

(assert (forall ((s1 State) (s2 State)) (=> (transitionCondition s1 s2) (reachable s1 s2))))
;(assert (forall ((s1 State) (s2 State)) (=> (not (transitionCondition s1 s2)) (not (reachable s1 s2)))))

(assert 
	(forall ((s1 State) (s2 State) (s3 State)) 
		(=> (and (reachable s1 s2) (reachable s2 s3)) (reachable s1 s3))
	)
)

(assert (exists ((s1 State)) (and (reachable S0 s1) (errorCondition s1) (not (= s1 nil)))))

(assert (initial S0))
  
;(assert 
;	(and
;		(initial S0) (not (= S0 nil))
;  		(transitionCondition S0 S1) 
;  		(or 
;  			(and (errorCondition S1) (= S2 nil))
;  			(and 
;  				(not (errorCondition S1)) (transitionCondition S1 S2) (not (= S1 nil)) 
;  				(or 
;  					(and (errorCondition S2) (= S3 nil))
;  					(and (not (errorCondition S2)) (transitionCondition S2 S3) (errorCondition S3))
;  				)
;  			)
  ;(transitionCondition S2 S3) (not (errorCondition S3))
  ;(transitionCondition S3 S4) (not (errorCondition S4))
  ;(transitionCondition S4 S5) (not (errorCondition S5))
  ;(transitionCondition S5 S6) (not (errorCondition S6))
  ;(transitionCondition S6 S7) (not (errorCondition S7))
  ;(transitionCondition S7 S8) (not (errorCondition S8))
  ;(transitionCondition S8 S9) (not (errorCondition S9))
  ;(transitionCondition S9 S10) (not (errorCondition S10))
  ;(transitionCondition S10 S11) (errorCondition S11)
;		)
;	)
;)

;(push 1)

(check-sat)
(get-model)
;(get-value (S0 S1 S2 S3)); S3 S4 S5 S6 S7 S8 S9 S10 S11))
