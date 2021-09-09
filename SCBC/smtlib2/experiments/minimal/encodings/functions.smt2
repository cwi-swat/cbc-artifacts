(define-sort State () Int)

(declare-fun counter (State) Int)
(declare-fun param (State) Int)

(define-fun increment ((current State) (next State)) Bool
	(and 
		(= (param next) 1)
		(= (counter next) (+ (counter current) (param next)))
	)
)

(define-fun decrement ((current State) (next State)) Bool
	(and 
		(= (param next) 1)
		(= (counter next) (- (counter current) (param next)))
	)
)

(define-fun transitionCondition ((current State) (next State)) Bool
	(and 
		(or
			(increment current next)	
			(decrement current next)
		)
		(= next (+ current 1))
		;(< next 17)
	)
)

(define-fun safetyCondition ((state State)) Bool
	(and 
		(< (counter state) 25)
		(> (counter state) (- 25))
	)
)

(define-fun initialCondition ((state State)) Bool
	(and 
		(= (counter state) 0)
		(= state 0)
	)
)

(push 1)

(declare-const s0 State)

(assert (initialCondition s0))

(assert (not (safetyCondition s0)))

(check-sat)

(pop 1)

(push 1)

(declare-const s0 State)
(declare-const s1 State)
;(declare-const s2 State)

(assert (safetyCondition s0))
;(assert (safetyCondition s1))

(assert (transitionCondition s0 s1))
;(assert (transitionCondition s1 s2))

(assert (not (safetyCondition s1)))

(check-sat)

(pop 1)

(push 1)

(declare-const s0 State)
(declare-const s1 State)

(assert (initialCondition s0))
(assert (transitionCondition s0 s1))

(assert (not (safetyCondition s1)))

(check-sat)

(pop 1)


;(push 1)
;
;(declare-fun distance (State State) Int)
;
;; step is part of from transitive closure
;(assert
;	(forall ((s1 State) (s2 State)) 
;		(= (transitionCondition s1 s2) (= (distance s1 s2) 1))
;	)
;)
;
;; transitivity
;(assert
;	(forall ((s1 State) (s2 State) (s3 State))
;		(=> (and (> (distance s1 s2) 0) (> (distance s2 s3) 0)) 
;			(> (distance s1 s3) 0))
;	)
;)
;
;; partial order
;(assert
;	(forall ((s1 State) (s3 State)) 
;		(=> (> (distance s1 s3) 1)
;			(exists ((s2 State))
;				(and 
;					(= (distance s1 s2) 1) 
;					(= (distance s1 s3) (+ 1 (distance s2 s3))))
;			)
;		)
;	)
;)
;
;(declare-const initialState State)
;(assert (initialCondition initialState))
;
;(assert
;	(exists ((s State))
;		(and 
;			(> (distance initialState s) 0) 
;			(not (safetyCondition s))
;		)
;	)
;)
;
;;(check-sat)
;;(get-model)
;
;;(eval (counter 0))
;;(eval (counter 1))
;;(eval (counter 2))
;;(eval (counter 3))
;;(eval (counter 4))
;;(eval (counter 5))
;;(eval (counter 6))
;;(eval (counter 7))
;;
;;(pop 1)
;
;(push 1)
;
;(declare-const s0 State)
;(declare-const s1 State)
;(declare-const s2 State)
;(declare-const s3 State)
;(declare-const s4 State)
;(declare-const s5 State)
;(declare-const s6 State)
;(declare-const s7 State)
;(declare-const s8 State)
;(declare-const s9 State)
;(declare-const s10 State)
;(declare-const s11 State)
;(declare-const s12 State)
;(declare-const s13 State)
;(declare-const s14 State)
;(declare-const s15 State)
;(declare-const s16 State)
;(declare-const s17 State)
;(declare-const s18 State)
;(declare-const s19 State)
;(declare-const s20 State)
;(declare-const s21 State)
;(declare-const s22 State)
;(declare-const s23 State)
;(declare-const s24 State)
;(declare-const s25 State)
;
;(assert (initialCondition s0))
;(assert (transitionCondition s0 s1))
;(assert (transitionCondition s1 s2))
;(assert (transitionCondition s2 s3))
;(assert (transitionCondition s3 s4))
;(assert (transitionCondition s4 s5))
;(assert (transitionCondition s5 s6))
;(assert (transitionCondition s6 s7))
;(assert (transitionCondition s7 s8))
;(assert (transitionCondition s8 s9))
;(assert (transitionCondition s9 s10))
;(assert (transitionCondition s10 s11))
;(assert (transitionCondition s11 s12))
;(assert (transitionCondition s12 s13))
;(assert (transitionCondition s13 s14))
;(assert (transitionCondition s14 s15))
;(assert (transitionCondition s15 s16))
;(assert (transitionCondition s16 s17))
;(assert (transitionCondition s17 s18))
;(assert (transitionCondition s18 s19))
;(assert (transitionCondition s19 s20))
;(assert (transitionCondition s20 s21))
;(assert (transitionCondition s21 s22))
;(assert (transitionCondition s22 s23))
;(assert (transitionCondition s23 s24))
;(assert (transitionCondition s24 s25))
;
;(assert (safetyCondition s0))
;(assert (safetyCondition s1))
;(assert (safetyCondition s2))
;(assert (safetyCondition s3))
;(assert (safetyCondition s4))
;(assert (safetyCondition s5))
;(assert (safetyCondition s6))
;(assert (safetyCondition s7))
;(assert (safetyCondition s8))
;(assert (safetyCondition s9))
;(assert (safetyCondition s10))
;(assert (safetyCondition s11))
;(assert (safetyCondition s12))
;(assert (safetyCondition s13))
;(assert (safetyCondition s14))
;(assert (safetyCondition s15))
;(assert (safetyCondition s16))
;(assert (safetyCondition s17))
;(assert (safetyCondition s18))
;(assert (safetyCondition s18))
;(assert (safetyCondition s19))
;(assert (safetyCondition s20))
;(assert (safetyCondition s21))
;(assert (safetyCondition s22))
;(assert (safetyCondition s23))
;(assert (safetyCondition s24))
;(assert (not (safetyCondition s25)))
;
;(check-sat)
;;(get-info :all-statistics)
;
;(eval (counter s0))
;(eval (counter s1))
;(eval (counter s2))
;(eval (counter s3))
;(eval (counter s4))
;(eval (counter s5))
;(eval (counter s6))
;(eval (counter s7))
;(eval (counter s8))
;(eval (counter s9))
;(eval (counter s10))
;(eval (counter s11))
;(eval (counter s12))
;(eval (counter s13))
;(eval (counter s14))
;(eval (counter s15))
;(eval (counter s16))
;(eval (counter s17))
;(eval (counter s18))
;(eval (counter s19))
;(eval (counter s20))
;(eval (counter s21))
;(eval (counter s22))
;(eval (counter s23))
;(eval (counter s24))
;(eval (counter s25))
;
;(pop 1)

;(push 1)
;
;(declare-const s0 State)
;(declare-const s1 State)
;(declare-const s2 State)
;(declare-const s3 State)
;(declare-const s4 State)
;(declare-const s5 State)
;(declare-const s6 State)
;(declare-const s7 State)
;(declare-const s8 State)
;(declare-const s9 State)
;(declare-const s10 State)
;(declare-const s11 State)
;(declare-const s12 State)
;(declare-const s13 State)
;(declare-const s14 State)
;(declare-const s15 State)
;(declare-const s16 State)
;(declare-const s17 State)
;(declare-const s18 State)
;(declare-const s19 State)
;(declare-const s20 State)
;(declare-const s21 State)
;(declare-const s22 State)
;(declare-const s23 State)
;(declare-const s24 State)
;(declare-const s25 State)
;
;(assert 
;	(and
;		(initialCondition s0)
;  		(transitionCondition s0 s1) 
;    		(or (not (safetyCondition s1))  
;  			(and (safetyCondition s1) (transitionCondition s1 s2)
;  			
;  			(or (not (safetyCondition s2)) 
;  			(and (safetyCondition s2) (transitionCondition s2 s3)
;
;  			(or (not (safetyCondition s3))
;  			(and (safetyCondition s3) (transitionCondition s3 s4)
;
;  			(or (not (safetyCondition s4))
;  			(and (safetyCondition s4) (transitionCondition s4 s5)
;
;  			(or (not (safetyCondition s5)) 
;  			(and (safetyCondition s5) (transitionCondition s5 s6)
;  			
;  			(or (not (safetyCondition s6))
;  			(and (safetyCondition s6) (transitionCondition s6 s7)
;  			
;  			(or (not (safetyCondition s7))
;  			(and (safetyCondition s7) (transitionCondition s7 s8)
;  			
;  			(or (not (safetyCondition s8))
;  			(and (safetyCondition s8) (transitionCondition s8 s9)
;  			
;  			(or (not (safetyCondition s9))
;  			(and (safetyCondition s9) (transitionCondition s9 s10)
;
;  			(or (not (safetyCondition s10))	
;  			(and (safetyCondition s10) (transitionCondition s10 s11)
;
;  			(or (not (safetyCondition s11))
;  			(and (safetyCondition s11) (transitionCondition s11 s12)
;
;  			(or (not (safetyCondition s12))
;  			(and (safetyCondition s12) (transitionCondition s12 s13)
;
;  			(or (not (safetyCondition s13))
;  			(and (safetyCondition s13) (transitionCondition s13 s14)
;
;  			(or (not (safetyCondition s14))
;  			(and (safetyCondition s14) (transitionCondition s14 s15)
;
;  			(or (not (safetyCondition s15))
;  			(and (safetyCondition s15) (transitionCondition s15 s16)
;
;  			(or (not (safetyCondition s16))
;  			(and (safetyCondition s16) (transitionCondition s16 s17)
;
;  			(or (not (safetyCondition s17))
;  			(and (safetyCondition s17) (transitionCondition s17 s18)
;
;  			(or (not (safetyCondition s18))
;  			(and (safetyCondition s18) (transitionCondition s18 s19)
;
;  			(or (not (safetyCondition s19))
;  			(and (safetyCondition s19) (transitionCondition s19 s20)
;
;  			(or (not (safetyCondition s20))
;  			(and (safetyCondition s20) (transitionCondition s20 s21)
;
;  			(or (not (safetyCondition s21))
;  			(and (safetyCondition s21) (transitionCondition s21 s22)
;
;  			(or (not (safetyCondition s22))
;  			(and (safetyCondition s22) (transitionCondition s22 s23)
;
;  			(or (not (safetyCondition s23))
;  			(and (safetyCondition s23) (transitionCondition s23 s24)
;
;  			(or (not (safetyCondition s24))
;  			(and (safetyCondition s24) (transitionCondition s24 s25) (not (safetyCondition s25))) 
;
;		)))))))))))))))))))))))))))))))))))))))))))))))
;	)
;)
;
;(check-sat)
;(get-info :all-statistics)
;
;(eval (counter s0))
;(eval (safetyCondition s0))
;
;(eval (counter s1))
;(eval (safetyCondition s1))
;
;(eval (counter s2))
;(eval (safetyCondition s2))
;
;(eval (counter s3))
;(eval (safetyCondition s3))
;
;(eval (counter s4))
;(eval (safetyCondition s4))
;
;(eval (counter s5))
;(eval (safetyCondition s5))
;
;(eval (counter s6))
;(eval (safetyCondition s6))
;
;(eval (counter s7))
;(eval (safetyCondition s7))
;
;(eval (counter s8))
;(eval (safetyCondition s8))
;
;(eval (counter s9))
;(eval (safetyCondition s9))
;
;(eval (counter s10))
;(eval (safetyCondition s10))
;
;(eval (counter s11))
;(eval (safetyCondition s11))
;
;(eval (counter s12))
;(eval (safetyCondition s12))
;
;(eval (counter s13))
;(eval (safetyCondition s13))
;
;(eval (counter s14))
;(eval (safetyCondition s14))
;
;(eval (counter s15))
;(eval (safetyCondition s15))
;
;(eval (counter s16))
;(eval (safetyCondition s16))
;
;(eval (counter s17))
;(eval (safetyCondition s17))
;
;(eval (counter s18))
;(eval (safetyCondition s18))
;
;(eval (counter s19))
;(eval (safetyCondition s19))
;
;(eval (counter s20))
;(eval (safetyCondition s20))
;
;(eval (counter s21))
;(eval (safetyCondition s21))
;
;(eval (counter s22))
;(eval (safetyCondition s22))
;
;(eval (counter s23))
;(eval (safetyCondition s23))
;
;(eval (counter s24))
;(eval (safetyCondition s24))
;
;(eval (counter s25))
;(eval (safetyCondition s25))
;
;(pop 1)
 