; Experiments with Time and Time based values
; In this example time starts at 0 and ends at 9

(define-sort Time () Int)

(declare-datatypes (T) ((Maybe (some (val T)) none))) 

(define-sort TimeBased (T) (Array Time (Maybe T)))

(define-fun getTimeBasedVal ((b (TimeBased Int)) (t Time)) Int
	(ite (> t 9) 0 
	(ite (not (= (select b t) none)) (val (select b t))
	(ite (and (>= (- t 1) 0) (not (= (select b (- t 1)) none))) (val (select b (- t 1)))
	(ite (and (>= (- t 2) 0) (not (= (select b (- t 2)) none))) (val (select b (- t 2)))
	(ite (and (>= (- t 3) 0) (not (= (select b (- t 3)) none))) (val (select b (- t 3)))
	(ite (and (>= (- t 4) 0) (not (= (select b (- t 4)) none))) (val (select b (- t 4)))
	(ite (and (>= (- t 5) 0) (not (= (select b (- t 5)) none))) (val (select b (- t 5)))
	(ite (and (>= (- t 6) 0) (not (= (select b (- t 6)) none))) (val (select b (- t 6)))
	(ite (and (>= (- t 7) 0) (not (= (select b (- t 7)) none))) (val (select b (- t 7)))
	(ite (and (>= (- t 8) 0) (not (= (select b (- t 8)) none))) (val (select b (- t 8)))
	(ite (and (>= (- t 9) 0) (not (= (select b (- t 9)) none))) (val (select b (- t 9)))
	0
	))))))))))) 
)


(define-fun calcInterest ((i Int)) Real
	(/ (* (/ (to_real i) 100) 2) 365) 	
)

(define-fun calcAccumulatedInterest ((b (TimeBased Int)) (from Time) (to Time)) Int
	(let ((v1 (getTimeBasedVal b from))
		  (v2 (ite (<= (+ from 1) to) (getTimeBasedVal b (+ from 1)) 0))
		  (v3 (ite (<= (+ from 2) to) (getTimeBasedVal b (+ from 2)) 0))
		  (v4 (ite (<= (+ from 3) to) (getTimeBasedVal b (+ from 3)) 0))
		  (v5 (ite (<= (+ from 4) to) (getTimeBasedVal b (+ from 4)) 0))
		  (v6 (ite (<= (+ from 5) to) (getTimeBasedVal b (+ from 5)) 0))
		  (v7 (ite (<= (+ from 6) to) (getTimeBasedVal b (+ from 6)) 0))
		  (v8 (ite (<= (+ from 7) to) (getTimeBasedVal b (+ from 7)) 0))
		  (v9 (ite (<= (+ from 8) to) (getTimeBasedVal b (+ from 8)) 0)))
		  
		  (to_int (+ 
		  	(calcInterest v1) 
		  	(calcInterest v2) 
		  	(calcInterest v3)
		  	(calcInterest v4) 
		  	(calcInterest v5) 
		  	(calcInterest v6) 
		  	(calcInterest v7) 
		  	(calcInterest v8) 
		  	(calcInterest v9)
		  ))
	)		 	
)

(declare-const b1 (TimeBased Int))
(declare-const b2 (TimeBased Int))
(declare-const b3 (TimeBased Int))

(assert (= b1 ((as const (TimeBased Int)) none)))
(assert (= (store b1 1 (some 1000)) b2)) 
(assert (= (store b2 4 (some 10000)) b3)) 

(check-sat)

(get-value ((getTimeBasedVal b3 9)))
(get-value ((getTimeBasedVal b3 1)))
(get-value ((getTimeBasedVal b3 0)))
(get-value ((getTimeBasedVal b2 9)))

(get-value ((calcAccumulatedInterest b3 4 6)))

