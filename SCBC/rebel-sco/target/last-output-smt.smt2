(define-sort Period () Int)
(define-sort Term () Int)
(define-sort Currency () String)
(define-sort Percentage () Int)
(define-sort Frequency () Int)
(declare-datatypes () (  ( IBAN (consIBAN (countryCode String) (checksum Int) (accountNumber String)) ) ))
(declare-datatypes () (  ( Money (consMoney (currency Currency) (amount Int)) ) ))
(declare-datatypes () (  ( Date (consDate (date Int) (month Int) (year Int)) (undefDate) ) ))
(declare-datatypes () (  ( Time (consTime (hour Int) (minutes Int) (seconds Int)) (undefTime) ) ))
(define-sort Map ( T1 T2) ( Array T1 T2))
(define-fun date ( (i Int)) Int
  i)
(define-fun + ( (s1 String) (s2 String)) String
  (str.++  s1 s2))
(define-fun > ( (d1 Date) (d2 Date)) Bool
  (or (>  (year  d1) (year  d2)) (and (=  (year  d1) (year  d2))
    (>  (month  d1) (month  d2))) (and (=  (year  d1) (year  d2))
    (=  (month  d1) (month  d2))
    (>  (date  d1) (date  d2)))))
(define-fun < ( (d1 Date) (d2 Date)) Bool
  (or (<  (year  d1) (year  d2)) (and (=  (year  d1) (year  d2))
    (<  (month  d1) (month  d2))) (and (=  (year  d1) (year  d2))
    (=  (month  d1) (month  d2))
    (<  (date  d1) (date  d2)))))
(define-fun >= ( (d1 Date) (d2 Date)) Bool
  (or (=  d1 d2) (>  d1 d2)))
(define-fun <= ( (d1 Date) (d2 Date)) Bool
  (or (=  d1 d2) (<  d1 d2)))
(declare-datatypes () (  ( StateLabel (Opened) (Closed) (Init) ) ))
(declare-datatypes () (  ( Event (Withdraw (withdraw-amount Int)) (Interest (interest-currentInterest Int)) (Deposit (deposit-amount Int)) (Open ) ) ))
(declare-datatypes () (  ( State (State (label StateLabel) (now Int) (accountNumber Int) (balance Int)) ) ))
(define-fun pre_withdraw ( (param_this State) (param_amount Int)) Bool
  (and (or (is-Opened  (label  param_this)))
    (> param_amount 0)
    (>= (- (balance  param_this)  param_amount) 0)))
(define-fun post_withdraw ( (param_this State) (param_post_state State) (param_amount Int)) Bool
  (and (is-Opened  (label  param_post_state))
    (= (balance  param_post_state) (- (balance  param_this)  param_amount))
    (= (accountNumber  param_this) (accountNumber  param_post_state))
    (= (now  param_post_state) (+ (now  param_this)  1))))
(define-fun pre_interest ( (param_this State) (param_currentInterest Int)) Bool
  (and (or (is-Opened  (label  param_this)))
    (<= param_currentInterest 10)))
(define-fun post_interest ( (param_this State) (param_post_state State) (param_currentInterest Int)) Bool
  (and (is-Opened  (label  param_post_state))
    (= (balance  param_post_state) (+ (balance  param_this)  (* (balance  param_this)  param_currentInterest)))
    (= (accountNumber  param_this) (accountNumber  param_post_state))
    (= (now  param_post_state) (+ (now  param_this)  1))))
(define-fun pre_deposit ( (param_this State) (param_amount Int)) Bool
  (and (or (is-Opened  (label  param_this)))
    (> param_amount 0)))
(define-fun post_deposit ( (param_this State) (param_post_state State) (param_amount Int)) Bool
  (and (is-Opened  (label  param_post_state))
    (= (balance  param_post_state) (+ (balance  param_this)  param_amount))
    (= (accountNumber  param_this) (accountNumber  param_post_state))
    (= (now  param_post_state) (+ (now  param_this)  1))))
(define-fun pre_open ( (param_this State)) Bool
  (and (or (is-Init  (label  param_this)))))
(define-fun post_open ( (param_this State) (param_post_state State)) Bool
  (and (is-Opened  (label  param_post_state))
    (= (balance  param_post_state) 0)
    (= (accountNumber  param_this) (accountNumber  param_post_state))
    (= (now  param_post_state) (+ (now  param_this)  1))))
(define-fun pre ( (event Event) (pre_state State)) Bool
  (ite (is-Open  event)
    (pre_open  pre_state) (ite (is-Deposit  event)
    (pre_deposit  pre_state (deposit-amount  event)) (ite (is-Interest  event)
    (pre_interest  pre_state (interest-currentInterest  event)) (ite (is-Withdraw  event)
    (pre_withdraw  pre_state (withdraw-amount  event)) false)))))
(define-fun post ( (event Event) (pre_state State) (post_state State)) Bool
  (ite (is-Open  event)
    (post_open  pre_state post_state) (ite (is-Deposit  event)
    (post_deposit  pre_state post_state (deposit-amount  event)) (ite (is-Interest  event)
    (post_interest  pre_state post_state (interest-currentInterest  event)) (ite (is-Withdraw  event)
    (post_withdraw  pre_state post_state (withdraw-amount  event)) false)))))
(define-fun event ( (event Event) (pre_state State) (post_state State)) Bool
  (and (pre  event pre_state)
    (post  event pre_state post_state)))