(set-logic HORN)

(declare-datatypes () (  ( Dec1Params (consDec1Params  (decWith Int) (_toState Int))  ) )) ;(noDec1Params)
(declare-datatypes () (  ( InitParams (consInitParams  (_toState Int))  ) )) ;(noInitParams)
(declare-datatypes () (  ( Inc1Params (consInc1Params  (incWith Int) (_toState Int)) ) )) ;(noInc1Params)
(declare-datatypes () (  ( Counter (consCounter  (counter Int) (_step Int) (_state Int) (p Bool)  ) ))) ;(noCounter)
(declare-datatypes () (  ( State (consState (c1 Counter) (dec1Params Dec1Params) (initParams InitParams) (inc1Params Inc1Params)) ) ))

(define-fun dec1 ( (current State) (next State)) Bool 
	(and 
		(> (decWith (dec1Params next)) 0) 
		(< (decWith (dec1Params next)) 2) 
		(= (_state (c1 current)) 1) 
		(= (_toState (dec1Params next)) 1) 

		(= (counter (c1 next)) (- (counter (c1 current)) (decWith (dec1Params next)))) 
		(= (_step (c1 next)) 2) 
		(= (p (c1 next)) (p (c1 current)))

		(= (_state (c1 next)) (_toState (dec1Params next)))
		(> (counter (c1 next)) (- 100))
	)
)

(define-fun init ( (current State) (next State)) Bool 
	(and 
		(= (_toState (initParams next)) 1) 
		
		;(forall ((b (_ BitVec 1))) 
		;	(ite (= b #b0) 
		;		(and 
		;			(= (counter (select (counter next) b)) 0) 
		;			(= (_step (select (counter next) b)) 1) 
		;			(= (_state (select (counter next) b)) (_toState2 (initParams next)))
		;		)
		;		(= (select (counter next) b) (select (counter current) b)) 
		;	)
		;)
		
		;(= (counter next) 
		;	(store (counter current) 
		;		#b0 
		;		(consCounter 0 1 (_toState2 (initParams next)))))
			
		(= (counter (c1 next)) 0) 
		(= (_step (c1 next)) 1) 
		(= (_state (c1 next)) (_toState (initParams next)))
	)
 )

(define-fun inc1 ( (current State) (next State)) Bool 
	(and 
		(> (incWith (inc1Params next)) 0) 
		(< (incWith (inc1Params next)) 2) 
		(= (_state (c1 current)) 1) 
		(= (_toState (inc1Params next)) 1) 
		(= (counter (c1 next)) (+ (counter (c1 current)) (incWith (inc1Params next)))) 
		(= (_step (c1 next)) 3) 
		(= (_state (c1 next)) (_toState (inc1Params next)))
		;(ite (> (counter (c1 next)) 20) (not (p (c1 next))) (p (c1 next)))
		(< (counter (c1 next)) 100)
	)
)

(define-fun notBelow ( (state State)) Bool 
	(> (counter (c1 state)) (- 1000))
)

(define-fun notAbove ( (state State)) Bool 
	(and 
		(< (counter (c1 state)) 1000)
		;(p (c1 state))
	)
)

(define-fun initial ( (state State)) Bool 
	(and 
		(= (_state (c1 state)) 0) 
		(= (counter (c1 state)) 0)
		(p (c1 state))
	)
)

(define-fun transitionCondition ( (current State) (next State)) Bool 
	(or 
		;(and 
			(dec1  current next) 
			;(not (= (dec1Params next) noDec1Params)) 
			;(= (initParams next) noInitParams) 
			;(= (inc1Params next) noInc1Params)
		;) 
		;(and 
			(init  current next) 
			;(= (dec1Params next) noDec1Params) 
			;(not (= (initParams next) noInitParams)) 
			;(= (inc1Params next) noInc1Params)
		;) 
		;(and 
			(inc1  current next) 
			;(= (dec1Params next) noDec1Params) 
			;(= (initParams next) noInitParams) 
			;(not (= (inc1Params next) noInc1Params))
		;)
	)
)

(define-fun errorCondition ( (state State)) Bool (or (not (notBelow  state)) (not (notAbove  state))))



(declare-fun reach (State) Bool)

(assert (forall ((s State)) (=> (initial s) (reach s))))

(assert (forall ((s1 State) (s2 State)) (=> (and (reach s1) (transitionCondition s1 s2)) (reach s2))))

(assert (forall ((s State)) (=> (reach s) (not (errorCondition s)))))

(check-sat)

(get-model)

(eval (forall ((s State)) (reach s)))


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
;(assert (initial  s0))
;(assert (and (transitionCondition  s0 s1) (not (errorCondition  s1))))
;(assert (and (transitionCondition  s1 s2) (not (errorCondition  s2))))
;(assert (and (transitionCondition  s2 s3) (not (errorCondition  s3))))
;(assert (and (transitionCondition  s3 s4) (not (errorCondition  s4))))
;(assert (and (transitionCondition  s4 s5) (not (errorCondition  s5))))
;(assert (and (transitionCondition  s5 s6) (not (errorCondition  s6))))
;(assert (and (transitionCondition  s6 s7) (not (errorCondition  s7))))
;(assert (and (transitionCondition  s7 s8) (not (errorCondition  s8))))
;(assert (and (transitionCondition  s8 s9) (not (errorCondition  s9))))
;(assert (and (transitionCondition  s9 s10) (not (errorCondition  s10))))
;(assert (and (transitionCondition  s10 s11) (not (errorCondition  s11))))
;(assert (and (transitionCondition  s11 s12) (not (errorCondition  s12))))
;(assert (and (transitionCondition  s12 s13) (not (errorCondition  s13))))
;(assert (and (transitionCondition  s13 s14) (not (errorCondition  s14))))
;(assert (and (transitionCondition  s14 s15) (not (errorCondition  s15))))
;(assert (and (transitionCondition  s15 s16) (not (errorCondition  s16))))
;(assert (and (transitionCondition  s16 s17) (not (errorCondition  s17))))
;(assert (and (transitionCondition  s17 s18) (not (errorCondition  s18))))
;(assert (and (transitionCondition  s18 s19) (not (errorCondition  s19))))
;(assert (and (transitionCondition  s19 s20) (not (errorCondition  s20))))
;(assert (and (transitionCondition  s20 s21) (not (errorCondition  s21))))
;(assert (and (transitionCondition  s21 s22) (not (errorCondition  s22))))
;(assert (and (transitionCondition  s22 s23) (not (errorCondition  s23))))
;(assert (and (transitionCondition  s23 s24) (not (errorCondition  s24))))
;(assert (and (transitionCondition  s24 s25) (errorCondition  s25)))
;(check-sat)
;(get-value ( s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 s25))