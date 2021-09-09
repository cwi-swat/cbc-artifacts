(define-fun daysInYear ((year Int)) Int 
  (ite (= (mod year 4) 0)
    (ite (= (mod year 100) 0)
      (ite (= (mod year 400) 0) 366 365)
      366)
  15)
)

(define-fun interest ((rate Int) (amount Int)) Int
  (div (* (div amount 100) rate) (daysInYear 2014))
)

(define-fun balance ((day Int)) Int
  (ite (< day 0) 0
   (ite (< day 5) 2000
      (ite (< day 10) 8000 10000)
    )

  )
)

(define-fun rates ((amount Int)) Int
  (ite (< amount 1001) 3
    (ite (< amount 10001) 2 1)
  )
)

(define-fun calc () Int
  (+ (interest (rates (balance 0)) (balance 0)) 
  (+ (interest (rates (balance 1)) (balance 1)) 
  (+ (interest (rates (balance 2)) (balance 2))
  (+ (interest (rates (balance 3)) (balance 3))
  (+ (interest (rates (balance 4)) (balance 4))
  (+ (interest (rates (balance 5)) (balance 5))
  (+ (interest (rates (balance 6)) (balance 6))
  (+ (interest (rates (balance 7)) (balance 7))
  (+ (interest (rates (balance 8)) (balance 8))
  (+ (interest (rates (balance 9)) (balance 9))
  (+ (interest (rates (balance 10)) (balance 10))
  (+ (interest (rates (balance 11)) (balance 11))
  (+ (interest (rates (balance 12)) (balance 12))
  (+ (interest (rates (balance 13)) (balance 13))
  (+ (interest (rates (balance 14)) (balance 14)) (balance 14)
  )))))))))))))))
)

(declare-const new.balance Int)
(assert (= new.balance calc))

(assert (= 10000 (balance 100)))

(check-sat)
(get-value (new.balance))
