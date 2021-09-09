(define-sort Time () Int)

(declare-datatypes () ((Date (consDate (year Int) (month Int) (day Int)))))

(define-fun _era ((y Int)) Int
	(div y 400)
)

(define-fun _dayOfYear ((m Int) (d Int)) Int 
	(+ (div (+ 2 (* 153 (+ m (ite (> m 2) (- 3) 9)))) 5) (- d 1))
)

(define-fun toTime ((d Date)) Time
	(let ((ay (ite (<= (month d) 2) (- (year d) (month d)) (year d))))
		(let ((era (_era ay)))
			(let ((yoe (- ay (* era 400))))
				(let ((doy (_dayOfYear (month d) (day d))))
					(let ((doe (+ (- (+ (* yoe 365) (div yoe 4)) (div yoe 100)) doy))) 
						(- (+ (* era 146097) doe) 719468)
					)
				)
			)
		)
	) 
)

(define-fun toDate ((t Time)) Date 
	(let ((at (+ t 719468))) 
		(let ((era (div (ite (>= at 0) at (- at 146096)) 146097)))
			(let ((doe (- at (* era 146097))))
				(let ((yoe (div (- (+ (- doe (div doe 1460)) (div doe 36524)) (div doe 146096)) 365)))
					(let ((doy (- doe (- (+ (* 365 yoe) (div yoe 4)) (div yoe 100)))))
						(let ((mp (div (+ (* 5 doy) 2) 153)))
							(let ((year (+ yoe (* era 400))))
								(let ((month (+ mp (ite (< mp 10) 3 (- 9)))))
									(consDate 
										(ite (<= month 2) (+ year 1) year) 
										month
										(+ (- doy (div (+ (* 153 mp) 2) 5)) 1)
									)
								)
							)
						)
					)
				)
			)
		)
	)
)

(define-fun toWeekDay ((t Time)) Int
	(ite (>= t (- 4)) (mod (+ t 4) 7) (+ (mod (+ t 5) 7) 6))
)

(define-sort State () Int) 

(declare-fun balance (State) Int)
(declare-fun time (State) Time)
(declare-fun date (State) Date)
(declare-fun stateNr (State) Int)
(declare-fun viaStep (State) Int)

(declare-fun pAmount (State) Int)

(define-fun initial ((st State)) Bool
	(and 
		(= (balance st) 10)
		(= (time st) 16826)
		(= (stateNr st) 1)
		(= (viaStep st) 0)
	)
)

(define-fun deposit ((cur State) (next State)) Bool
	(and
		; amount should be positive
		(> (pAmount next) 0) (< (pAmount next) 11)
		(= (balance next) (+ (balance cur) (pAmount next))) 
		; only possible on wednesday, or on the first of every month
		(or 
			(= (toWeekDay (time next)) 3) 
			;(= (day (toDate (time next))) 1)
		)
		(= (stateNr next) 1)
		(= (viaStep next) 1)	
	)
)

(define-fun withdraw ((cur State) (next State)) Bool
	(and
		(> (pAmount next) 0) (< (pAmount next) 11)
		(>= (- (balance cur) (pAmount next)) 0)
		(= (balance next) (- (balance cur) (pAmount next)))
		(= (toWeekDay (time next)) 1)
		(= (stateNr next) 1)
		(= (viaStep next) 2)	
	)
)

(define-fun close ((cur State) (next State)) Bool
	(and
		(= (balance cur) 0)
		(> (time next) (toTime (consDate 2016 12 1))) 
		(= (balance next) 0)
		(= (stateNr next) 2)
		(= (viaStep next) 3)			
	)
)

(define-fun transition ((cur State) (next State)) Bool
	(and 
		(< (time next) (+ 16826 366))
		(> (time next) (time cur))
		;(= (date next) (toDate (time next)))
		(or 
			(deposit cur next)
			(withdraw cur next)
			(close cur next)
		)
	)
)

(define-fun errorCondition ((st State)) Bool
	(or 
		(>= (balance st) 40)
		(= (stateNr st) 2)
	)
)

(declare-const S0 State)
(declare-const S1 State)
(declare-const S2 State)
(declare-const S3 State)
(declare-const S4 State)

(assert (and (initial S0) (not (errorCondition S0))))
;(assert (and (transition S0 S1) (errorCondition S1)))
(assert (and (transition S0 S1) (not (errorCondition S1))))
(assert (and (transition S1 S2) (not (errorCondition S2))))
(assert (and (transition S2 S3) (not (errorCondition S3))))
(assert (and (transition S3 S4) (errorCondition S4)))

(check-sat)

(get-value ((balance S0) (toDate (time S0)) (stateNr S0) (viaStep S0) 
			(balance S1) (toDate (time S1)) (stateNr S1) (viaStep S1)
			(balance S2) (toDate (time S2)) (stateNr S2) (viaStep S2)
			(balance S3) (toDate (time S3)) (stateNr S3) (viaStep S3)
			(balance S4) (toDate (time S4)) (stateNr S4) (viaStep S4)))