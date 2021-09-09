;(set-option :produce-unsat-cores true)
;(set-option :model.compact true)

(declare-datatypes () (  ( IncrementParams (consIncrementParams  (id Int) (toState Int)) (noIncrementParams) ) ))
(declare-datatypes () (  ( InitializeParams (consInitializeParams  (id Int) (toState Int)) (noInitializeParams) ) ))

(declare-datatypes () (  ( Counter (consCounter  (id Int) (current Int) (step Int) (state Int)) (noCounter) ) ))

(declare-datatypes () (  ( State (consState  (counters (Array Int Counter)) (nrOfCounters Int) (incrementParams IncrementParams) (initializeParams InitializeParams)) ) ))

(define-fun increment ( (current State) (next State)) Bool 
	(and 
		;(= (state (select (counters current) (id (incrementParams next))) 1) 
		(= (toState (incrementParams next)) 1) 
		;(not (= (counter current) noCounter)) 
		(= (counters next) (store (counters current) 
			(id (incrementParams next)) 
			(consCounter 
				(id (incrementParams next)) ;id
				(+ (current (select (counters current) (id (incrementParams next)))) 1) ;current counter
				2 ; step
				(toState (incrementParams next)) ; state
			) 
		))
		;(= (current (counter next)) (+ (current (counter current)) 1)) 
		;(= (step (counter next)) 2) 
		(not (= (select (counters current) (id (incrementParams next))) noCounter)) 
		;(= (state (counter next)) (toState (incrementParams next)))
	)
)

(define-fun initialize ( (current State) (next State)) Bool 
	(and
		(= (counters next) (store (counters current) 
			(id (initializeParams next)) 
			(consCounter (id (initializeParams next)) 0 1 (toState (initializeParams next))) ))
		;(not (= (counter next) noCounter)) 
		(= (select (counters current) (id (initializeParams next))) noCounter) 

		(= (toState (initializeParams next)) 1) 
		(= (nrOfCounters next) (+ (nrOfCounters current) 1))
		;(= (current (counter next)) 0) 
		;(= (step (counter next)) 1) 
		;(= (state (counter next)) (toState (initializeParams next)))
	)
)

(define-fun belowTwo ( (state State)) Bool 
	(and 
		(< (current (select (counters state) 0) ) 2)
		(< (current (select (counters state) 1) ) 2)
		(< (current (select (counters state) 2) ) 2)
		(< (current (select (counters state) 3) ) 2)
		(< (current (select (counters state) 4) ) 2)
	)
)

(define-fun maxOneCounter ( (state State)) Bool
	(< (nrOfCounters state) 2)
)

(define-fun initial ( (state State)) Bool 
	(and 
		(= (incrementParams state) noIncrementParams) 
		(= (initializeParams state) noInitializeParams)
		(= (nrOfCounters state) 0)

		(= (select (counters state) 0) noCounter)
		(= (select (counters state) 1) noCounter)
		(= (select (counters state) 2) noCounter)
		(= (select (counters state) 3) noCounter)
		(= (select (counters state) 4) noCounter)
	)
)

(define-fun transitionCondition ( (current State) (next State)) Bool 
	(or 
		(and 
			(increment current next) 
			(not (= (incrementParams next) noIncrementParams)) 
			(= (initializeParams next) noInitializeParams)
			(= (nrOfCounters next) (nrOfCounters current))
			(and 
				(>= (id (incrementParams next)) 0)
				(< (id (incrementParams next)) 5)
			)
		) 
		(and 
			(initialize  current next) 
			(= (incrementParams next) noIncrementParams) 
			(not (= (initializeParams next) noInitializeParams))
			(= (id (initializeParams next)) (nrOfCounters current))
			(< (nrOfCounters current) 5)
			(>= (nrOfCounters current) 0)
		)
	)
)

(define-fun errorCondition ( (state State)) Bool 
	(or
		(not (belowTwo state)) 
		(not (maxOneCounter state))
	)
)

(push 1)

(declare-const s1 State)
(declare-const s2 State)
(declare-const s3 State)

(assert (initial s1))
(assert (transitionCondition s1 s2))
(assert (not (errorCondition s2)))
(assert 
	(and 
		(initialize s2 s3) 
		(= (incrementParams s3) noIncrementParams) 
		(not (= (initializeParams s3) noInitializeParams))
		(= (id (initializeParams s3)) (nrOfCounters s2))
		(< (nrOfCounters s2) 5)
		(>= (nrOfCounters s2) 0)
	)
)
;(assert (errorCondition s3))

(check-sat)
;(get-model)

(pop 1)

(push 1)

(declare-const s1 State)
(declare-const s2 State)
(declare-const s3 State)
;(declare-const s4 State)

(assert (initial s1))
(assert (and (transitionCondition s1 s2) (not (errorCondition s2))))
;(assert (! (and (transitionCondition s2 s3) (not (errorCondition s3))) :named trans_2))
(assert (and (transitionCondition s2 s3) (errorCondition s3)))
;(assert (! (and (transitionCondition s3 s4) (errorCondition s4)) :named trans_3))

(check-sat)
;(get-unsat-core)
(get-model)
(pop 1)

(push 1)

(assert (exists ((s1 State) (s2 State))
	(and (not (errorCondition s1)) (transitionCondition s1 s2) (errorCondition s2))
))

(check-sat)
(get-model)
(pop 1)