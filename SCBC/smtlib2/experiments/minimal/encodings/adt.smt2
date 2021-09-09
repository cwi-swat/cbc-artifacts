(set-logic HORN)

;(query :engine duality :print-certificate true)

(declare-datatypes () ((Param (consP (val Int)))))

(declare-datatypes () ((State (cons (counter Int) (param Param)))))

;(declare-fun param (State) Int)

(define-fun increment ((current State) (next State)) Bool
	(and 
		(> (val (param next)) 0)
		(< (val (param next)) 2)
		(= (counter next) (+ (counter current) (val (param next))))
	)
)

(define-fun decrement ((current State) (next State)) Bool
	(and 
		(= (val (param next)) 1)
		(= (counter next) (- (counter current) (val (param next))))
	)
)

(define-fun transitionCondition ((current State) (next State)) Bool
	(and 
		(or
			(increment current next)
			(decrement current next)
		)
	)
)

(define-fun safetyCondition ((state State)) Bool
	(and 
		(< (counter state) 100)
		(> (counter state) (- 100))
	)
)

(define-fun initialCondition ((state State)) Bool
	(= (counter state) 0)
)

;(push 1)

(declare-fun reach (State) Bool)

(assert (forall ((s State)) (=> (initialCondition s) (reach s))))

(assert (forall ((s1 State) (s2 State)) (=> (and (reach s1) (transitionCondition s1 s2)) (reach s2))))

(assert (forall ((s State)) (=> (reach s) (safetyCondition s))))

(check-sat)

(get-model)

;(pop 1)

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
;(get-model)