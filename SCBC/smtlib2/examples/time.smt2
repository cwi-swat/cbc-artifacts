; algorithms as described on http://howardhinnant.github.io/date_algorithms.html
; Time 0 = 1970-01-01 00:00

(define-sort Time () Int)

(define-sort OverTime (T) (Array Time T))

(declare-const startTime Time)
(declare-const entTime Time)

;(define-fun calc ((val (OverTime Int)) (from Time) (to Time) (inc Int) (func (Int Int))) Int
;	(let ((r1 (ite (and (>= startTime from) (<= startTime to)) (func 
;) 

(declare-datatypes () ((Date (consDate (year Int) (month Int) (day Int)))))
;(declare-datatypes () ((DateTime (consDateTime (year Int) (month Int) (day Int) (hour Int) (month Int) (seconds Int)))))

(define-fun _toDays ((t Time)) Int
	; there are 86400 seconds a day
	(div t 86400)
)

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

(define-fun convert((t Time) (d Date)) Bool
	(and 
		(= d (toDate t))
		(= t (toTime d))
	)		
)

(declare-const d Date)
(declare-const t Time)

;(assert (= d (consDate 2016 1 21)))
(assert (= t 16826))

;(assert (= t (toTime (consDate 2016 1 21))))
(assert (= d (toDate t)))

(check-sat)
(get-value (d t))
