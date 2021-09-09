(declare-datatypes () (  ( Date (consDate  (date Int) (month Int) (year Int)) (undefDate) ) ))
(declare-datatypes () (  ( Time (consTime  (hour Int) (minutes Int) (seconds Int)) (undefTime) ) ))
(declare-datatypes () (  ( DateTime (consDateTime  (date Date) (time Time)) (undefDateTime) ) ))

(define-fun _dateToInt ( (date Date)) Int (ite (= date (consDate 2 8 2016)) 1 (ite (= date (consDate 3 8 2016)) 2 (ite (= date (consDate 4 8 2016)) 3 (ite (= date (consDate 5 8 2016)) 4 (ite (= date (consDate 6 8 2016)) 5 (ite (= date (consDate 7 8 2016)) 6 (ite (= date (consDate 8 8 2016)) 7 (ite (= date (consDate 9 8 2016)) 8 (ite (= date (consDate 10 8 2016)) 9 (ite (= date (consDate 11 8 2016)) 10 (ite (= date (consDate 12 8 2016)) 11 (ite (= date (consDate 13 8 2016)) 12 (ite (= date (consDate 14 8 2016)) 13 (ite (= date (consDate 15 8 2016)) 14 (ite (= date (consDate 16 8 2016)) 15 (ite (= date (consDate 17 8 2016)) 16 (ite (= date (consDate 18 8 2016)) 17 (ite (= date (consDate 19 8 2016)) 18 (ite (= date (consDate 20 8 2016)) 19 (ite (= date (consDate 21 8 2016)) 20 (ite (= date (consDate 22 8 2016)) 21 (ite (= date (consDate 23 8 2016)) 22 (ite (= date (consDate 24 8 2016)) 23 (ite (= date (consDate 25 8 2016)) 24 (ite (= date (consDate 26 8 2016)) 25 (ite (= date (consDate 27 8 2016)) 26 (ite (= date (consDate 28 8 2016)) 27 (ite (= date (consDate 29 8 2016)) 28 (ite (= date (consDate 30 8 2016)) 29 (ite (= date (consDate 31 8 2016)) 30 (- 1))))))))))))))))))))))))))))))))
(define-fun _timeToInt ( (time Time)) Int (ite (= time (consTime 1 0 0)) 1 (ite (= time (consTime 2 0 0)) 2 (ite (= time (consTime 3 0 0)) 3 (ite (= time (consTime 4 0 0)) 4 (ite (= time (consTime 5 0 0)) 5 (ite (= time (consTime 6 0 0)) 6 (ite (= time (consTime 7 0 0)) 7 (ite (= time (consTime 8 0 0)) 8 (ite (= time (consTime 9 0 0)) 9 (ite (= time (consTime 10 0 0)) 10 (ite (= time (consTime 11 0 0)) 11 (ite (= time (consTime 12 0 0)) 12 (ite (= time (consTime 13 0 0)) 13 (ite (= time (consTime 14 0 0)) 14 (ite (= time (consTime 15 0 0)) 15 (ite (= time (consTime 16 0 0)) 16 (ite (= time (consTime 17 0 0)) 17 (ite (= time (consTime 18 0 0)) 18 (ite (= time (consTime 19 0 0)) 19 (ite (= time (consTime 20 0 0)) 20 (ite (= time (consTime 21 0 0)) 21 (ite (= time (consTime 22 0 0)) 22 (ite (= time (consTime 23 0 0)) 23 (ite (= time (consTime 24 0 0)) 24 (- 1))))))))))))))))))))))))))
(define-fun _isValidDate ( (date Date)) Bool (and (>= (year  date) 1900) (<= (year  date) 2100) (>= (month  date) 1) (<= (month  date) 12) (>= (date  date) 1) (<= (date  date) 31) (not (= (_dateToInt  date) (- 1)))))
(define-fun _isValidTime ( (time Time)) Bool (and (>= (hour  time) 0) (<= (hour  time) 23) (>= (minutes  time) 0) (<= (minutes  time) 59) (>= (seconds  time) 0) (<= (seconds  time) 59)))

(declare-const x Date)
(declare-const y Date)

(assert (_isValidDate x))
(assert (_isValidDate y))

(assert (= (sub y x) 10))

(check-sat)

(get-value (x y))
