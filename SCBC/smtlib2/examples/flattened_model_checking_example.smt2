; This is an flattened encoding of a simple state containing a counter (the 'c' variable)
; There are two possible transitions between each state; increment and decrement
; both transitions contain data, the integer with which to in- or decrement 
; and guards on both the state; the counter should always be greater then or equal to 0
; and guards on the transition parameter; the parameter should be a value between 1 and 3 

; declaration of the counter
(declare-const c0 Int)
(declare-const c1 Int)
(declare-const c2 Int)
(declare-const c3 Int)
(declare-const c4 Int)

; declaration of the increment parameter
(declare-const inc0 Int)
(declare-const inc1 Int)
(declare-const inc2 Int)
(declare-const inc3 Int)

; declaration of the decrement parameter
(declare-const dec0 Int)
(declare-const dec1 Int)
(declare-const dec2 Int)
(declare-const dec3 Int)


(define-fun increment ((current Int) (next Int) (param Int)) Bool
	(and 
		(= next (+ current param))
		(>= next 0)
		(> param 0)
		(< param 2)
	)
)

(define-fun decrement ((current Int) (next Int) (param Int)) Bool
	(and 
		(= next (- current param))
		(>= next 0)
		(> param 0)
		(< param 2)
	)
)

(define-fun safetyCondition ((counter Int)) Bool
	(not (> counter 3))
)

; initial condition
(assert (= c0 0))

; transition conditions
(assert 
	(and
		(or ; first transition
			(and (increment c0 c1 inc0) (= dec0 (- 1)))
			(and (decrement c0 c1 dec0) (= inc0 (- 1)))
		)
		(or ; second transition
			(and (increment c1 c2 inc1) (= dec1 (- 1)))
			(and (decrement c1 c2 dec1) (= inc1 (- 1)))
		)
		(or ; third transition
			(and (increment c2 c3 inc2) (= dec2 (- 1)))
			(and (decrement c2 c3 dec2) (= inc2 (- 1)))
		)
		(or ; fourth transition, this is where the error should occur
			(and (increment c3 c4 inc3) (= dec3 (- 1)))
			(and (decrement c3 c4 dec3) (= inc3 (- 1)))		
		)
	)
)

; safety condition
(assert 
	(and 
		(safetyCondition c0) 
		(safetyCondition c1) 
		(safetyCondition c2) 
		(safetyCondition c3) 
		(not (safetyCondition c4))
	)
)

(check-sat)
(get-model)
