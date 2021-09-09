
(declare-datatypes () (  ( Dec1Params (consDec1Params  (decWith Int) (_toState Int)) (noDec1Params) ) ))
(declare-datatypes () (  ( InitParams (consInitParams  (_toState Int)) (noInitParams) ) ))
(declare-datatypes () (  ( Inc1Params (consInc1Params  (incWith Int) (_toState Int)) (noInc1Params) ) ))
(declare-datatypes () (  ( Counter (consCounter  (counter Int) (_state Int)) (noCounter) ) ))
(declare-datatypes () (  ( State (consState  (counter Counter)))))

(declare-fun decParams (State) Dec1Params) 
(declare-fun initParams (State) InitParams) 
(declare-fun incParams (State) Inc1Params)

(define-fun dec1_pre ( (current State) (next State)) Bool 
	(and 
		(> (decWith (decParams next)) 0) 
		(< (decWith (decParams next)) 2) 

		(not (= (counter current) noCounter)) 
		(and (= (_state (counter current)) 1) (= (_toState (decParams next)) 1)) 
	)
)

(define-fun dec1_post ( (current State) (next State)) Bool 
	(and 
		(= (- (counter (counter next)) (counter (counter current))) (- (decWith (decParams next)))) 
		(= (_state (counter next)) (_toState (decParams next)))
	)
)

(define-fun init_pre ( (current State) (next State)) Bool 
	(= (counter current) noCounter) 
)

(define-fun init_post ((current State) (next State)) Bool
	(and
		(= (_state (counter next)) (_toState (initParams next)))
		(= (_toState (initParams next)) 1) 
		(= (counter (counter next)) 0) 
	)
)

(define-fun inc1_pre ( (current State) (next State)) Bool 
	(and 
		(> (incWith (incParams next)) 0) 
		(< (incWith (incParams next)) 2) 
		(not (= (counter current) noCounter)) 
		(and (= (_state (counter current)) 1) (= (_toState (incParams next)) 1)) 
	)
)

(define-fun inc1_post ( (current State) (next State)) Bool 
	(and 
		(= (- (counter (counter next)) (counter (counter current))) (incWith (incParams next))) 
		(= (_state (counter next)) (_toState (incParams next)))
	)
)


(define-fun notBelow ( (state State)) Bool 
	(> (counter (counter state)) (- 25))
)

(define-fun notAbove ( (state State)) Bool 
	(< (counter (counter state)) 25)
)

(define-fun initial ( (state State)) Bool 
	(and 
		(= (counter state) noCounter) 
		(= (decParams state) noDec1Params) 
		(= (initParams state) noInitParams) 
		(= (incParams state) noInc1Params)
	)
)

(define-fun transitionCondition ( (current State) (next State)) Bool 
	(and
		(=> (init_post current next) (init_pre current next))
		(=> (inc1_post current next) (inc1_pre current next))
		(=> (dec1_post current next) (dec1_pre current next))
	)
)

(define-fun safetyCondition ( (state State)) Bool (and (notBelow  state) (notAbove  state)))

(declare-const s0 State)
(declare-const s1 State)
(declare-const s2 State)
(declare-const s3 State)
(declare-const s4 State)
(declare-const s5 State)
(declare-const s6 State)
(declare-const s7 State)
(declare-const s8 State)
(declare-const s9 State)
(declare-const s10 State)
(declare-const s11 State)
(declare-const s12 State)
(declare-const s13 State)
(declare-const s14 State)
(declare-const s15 State)
(declare-const s16 State)
(declare-const s17 State)
(declare-const s18 State)
(declare-const s19 State)

(assert (initial  s0))

(assert (=> (init_post s0 s1) (init_pre s0 s1)))
(assert (=> (inc1_post s0 s1) (inc1_pre s0 s1)))
(assert (=> (dec1_post s0 s1) (dec1_pre s0 s1)))

(assert (=> (init_post s1 s2) (init_pre s1 s2)))
(assert (=> (inc1_post s1 s2) (inc1_pre s1 s2)))
(assert (=> (dec1_post s1 s2) (dec1_pre s1 s2)))

(assert (=> (init_post s2 s3) (init_pre s2 s3)))
(assert (=> (inc1_post s2 s3) (inc1_pre s2 s3)))
(assert (=> (dec1_post s2 s3) (dec1_pre s2 s3)))

(assert (=> (init_post s3 s4) (init_pre s3 s4)))
(assert (=> (inc1_post s3 s4) (inc1_pre s3 s4)))
(assert (=> (dec1_post s3 s4) (dec1_pre s3 s4)))

(assert (=> (init_post s4 s5) (init_pre s4 s5)))
(assert (=> (inc1_post s4 s5) (inc1_pre s4 s5)))
(assert (=> (dec1_post s4 s5) (dec1_pre s4 s5)))

(assert (=> (init_post s5 s6) (init_pre s5 s6)))
(assert (=> (inc1_post s5 s6) (inc1_pre s5 s6)))
(assert (=> (dec1_post s5 s6) (dec1_pre s5 s6)))

(assert (=> (init_post s6 s7) (init_pre s6 s7)))
(assert (=> (inc1_post s6 s7) (inc1_pre s6 s7)))
(assert (=> (dec1_post s6 s7) (dec1_pre s6 s7)))

(assert (=> (init_post s7 s8) (init_pre s7 s8)))
(assert (=> (inc1_post s7 s8) (inc1_pre s7 s8)))
(assert (=> (dec1_post s7 s8) (dec1_pre s7 s8)))

(assert (=> (init_post s8 s9) (init_pre s8 s9)))
(assert (=> (inc1_post s8 s9) (inc1_pre s8 s9)))
(assert (=> (dec1_post s8 s9) (dec1_pre s8 s9)))

(assert (=> (init_post s9 s10) (init_pre s9 s10)))
(assert (=> (inc1_post s9 s10) (inc1_pre s9 s10)))
(assert (=> (dec1_post s9 s10) (dec1_pre s9 s10)))

(assert (=> (init_post s10 s11) (init_pre s10 s11)))
(assert (=> (inc1_post s10 s11) (inc1_pre s10 s11)))
(assert (=> (dec1_post s10 s11) (dec1_pre s10 s11)))

(assert (=> (init_post s11 s12) (init_pre s11 s12)))
(assert (=> (inc1_post s11 s12) (inc1_pre s11 s12)))
(assert (=> (dec1_post s11 s12) (dec1_pre s11 s12)))

(assert (=> (init_post s12 s13) (init_pre s12 s13)))
(assert (=> (inc1_post s12 s13) (inc1_pre s12 s13)))
(assert (=> (dec1_post s12 s13) (dec1_pre s12 s13)))

(assert (=> (init_post s13 s14) (init_pre s13 s14)))
(assert (=> (inc1_post s13 s14) (inc1_pre s13 s14)))
(assert (=> (dec1_post s13 s14) (dec1_pre s13 s14)))

(assert (=> (init_post s14 s15) (init_pre s14 s15)))
(assert (=> (inc1_post s14 s15) (inc1_pre s14 s15)))
(assert (=> (dec1_post s14 s15) (dec1_pre s14 s15)))

(assert (=> (init_post s15 s16) (init_pre s15 s16)))
(assert (=> (inc1_post s15 s16) (inc1_pre s15 s16)))
(assert (=> (dec1_post s15 s16) (dec1_pre s15 s16)))

(assert (=> (init_post s16 s17) (init_pre s16 s17)))
(assert (=> (inc1_post s16 s17) (inc1_pre s16 s17)))
(assert (=> (dec1_post s16 s17) (dec1_pre s16 s17)))

(assert (=> (init_post s17 s18) (init_pre s17 s18)))
(assert (=> (inc1_post s17 s18) (inc1_pre s17 s18)))
(assert (=> (dec1_post s17 s18) (dec1_pre s17 s18)))

(assert (=> (init_post s17 s19) (init_pre s18 s19)))
(assert (=> (inc1_post s17 s19) (inc1_pre s18 s19)))
(assert (=> (dec1_post s17 s19) (dec1_pre s18 s19)))


(assert (safetyCondition  s1))
(assert (safetyCondition  s2))
(assert (safetyCondition  s3))
(assert (safetyCondition  s4))
(assert (safetyCondition  s5))
(assert (safetyCondition  s6))
(assert (safetyCondition  s7))
(assert (safetyCondition  s8))
(assert (safetyCondition  s9))
(assert (safetyCondition  s10))
(assert (safetyCondition  s11))
(assert (safetyCondition  s12))
(assert (safetyCondition  s13))
(assert (safetyCondition  s14))
(assert (safetyCondition  s15))
(assert (safetyCondition  s16))
(assert (safetyCondition  s17))
(assert (safetyCondition  s18))
(assert (not (safetyCondition  s19)))
;(assert (and (transitionCondition  s19 s20) (not (safetyCondition  s20))))
;(assert (and (transitionCondition  s20 s21) (safetyCondition  s21)))
;(assert (and (transitionCondition  s21 s22) (not (safetyCondition  s22))))
;(assert (and (transitionCondition  s22 s23) (safetyCondition  s23)))
;(assert (and (transitionCondition  s23 s24) (not (safetyCondition  s24))))
;(assert (and (transitionCondition  s24 s25) (safetyCondition  s25)))
;(assert (and (transitionCondition  s25 s26) (safetyCondition  s26)))

(check-sat)
(get-value ( s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19))
(eval (initParams s1))