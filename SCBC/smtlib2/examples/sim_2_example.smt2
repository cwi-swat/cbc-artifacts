(define-sort Term () Int)
(define-sort Time () Int)
(define-sort Period () Int)
(define-sort Percentage () Int)
(define-sort Frequency () Int)
(define-sort Currency () Int)

(declare-datatypes () (  ( IBAN (consIBAN  (countryCode String) (checksum Int) (accountNumber String)) ) ))
(declare-datatypes () (  ( Money (consMoney  (currency String) (amount Int)) ) ))
(declare-datatypes () (  ( Date (consDate (date Int) (month Int) (year Int)) undefDate)))
 
(declare-sort State)
(declare-sort CreditTransfer) 

(declare-fun creditTransfer (State Int) CreditTransfer)
(declare-fun CreditTransfer_initialized (CreditTransfer) Bool)

(define-fun validDate ((date Date)) Bool
  (or
    (= date (consDate 1 7 2016))
    (= date (consDate 2 7 2016))
    (= date (consDate 3 7 2016))
    (= date (consDate 4 7 2016))
    (= date (consDate 5 7 2016))
    (= date (consDate 6 7 2016))
    (= date (consDate 7 7 2016))
    (= date (consDate 8 7 2016))
    (= date (consDate 9 7 2016))
    (= date (consDate 10 7 2016))
    (= date (consDate 11 7 2016))
    (= date (consDate 12 7 2016))
    (= date (consDate 13 7 2016))
    (= date (consDate 14 7 2016))
    (= date (consDate 15 7 2016))
    (= date (consDate 16 7 2016))
    (= date (consDate 17 7 2016))
    (= date (consDate 18 7 2016))
    (= date (consDate 19 7 2016))
    (= date (consDate 20 7 2016))
    (= date (consDate 21 7 2016))
    (= date (consDate 22 7 2016))
    (= date (consDate 23 7 2016))
    (= date (consDate 24 7 2016))
    (= date (consDate 25 7 2016))
    (= date (consDate 26 7 2016))
    (= date (consDate 27 7 2016))
    (= date (consDate 28 7 2016))
    (= date (consDate 29 7 2016))
    (= date (consDate 30 7 2016))
    (= date (consDate 31 7 2016))
  )
)

(define-fun validTime ((time Time)) Bool
  (and (>= time 0) (< time (* 86400 31)))
)

(define-fun timeToDate ((time Time)) Date 
  (ite (and (>= time (* 86400 0)) (< time (* 86400 1))) (consDate 1 7 2016)
  (ite (and (>= time (* 86400 1)) (< time (* 86400 2))) (consDate 2 7 2016)
  (ite (and (>= time (* 86400 2)) (< time (* 86400 3))) (consDate 3 7 2016)
  (ite (and (>= time (* 86400 3)) (< time (* 86400 4))) (consDate 4 7 2016)
  (ite (and (>= time (* 86400 4)) (< time (* 86400 5))) (consDate 5 7 2016)
  (ite (and (>= time (* 86400 5)) (< time (* 86400 6))) (consDate 6 7 2016)
  (ite (and (>= time (* 86400 6)) (< time (* 86400 7))) (consDate 7 7 2016)
  (ite (and (>= time (* 86400 7)) (< time (* 86400 8))) (consDate 8 7 2016)
  (ite (and (>= time (* 86400 8)) (< time (* 86400 9))) (consDate 9 7 2016)
  (ite (and (>= time (* 86400 9)) (< time (* 86400 10))) (consDate 10 7 2016)
  (ite (and (>= time (* 86400 10)) (< time (* 86400 11))) (consDate 11 7 2016)
  (ite (and (>= time (* 86400 11)) (< time (* 86400 12))) (consDate 12 7 2016)
  (ite (and (>= time (* 86400 12)) (< time (* 86400 13))) (consDate 13 7 2016)
  (ite (and (>= time (* 86400 13)) (< time (* 86400 14))) (consDate 14 7 2016)
  (ite (and (>= time (* 86400 14)) (< time (* 86400 15))) (consDate 15 7 2016)
  (ite (and (>= time (* 86400 15)) (< time (* 86400 16))) (consDate 16 7 2016)
  (ite (and (>= time (* 86400 16)) (< time (* 86400 17))) (consDate 17 7 2016)
  (ite (and (>= time (* 86400 17)) (< time (* 86400 18))) (consDate 18 7 2016)
  (ite (and (>= time (* 86400 18)) (< time (* 86400 19))) (consDate 19 7 2016)
  (ite (and (>= time (* 86400 19)) (< time (* 86400 20))) (consDate 20 7 2016)
  (ite (and (>= time (* 86400 20)) (< time (* 86400 21))) (consDate 21 7 2016)
  (ite (and (>= time (* 86400 21)) (< time (* 86400 22))) (consDate 22 7 2016)
  (ite (and (>= time (* 86400 22)) (< time (* 86400 23))) (consDate 23 7 2016)
  (ite (and (>= time (* 86400 23)) (< time (* 86400 24))) (consDate 24 7 2016)
  (ite (and (>= time (* 86400 24)) (< time (* 86400 25))) (consDate 25 7 2016)
  (ite (and (>= time (* 86400 25)) (< time (* 86400 26))) (consDate 26 7 2016)
  (ite (and (>= time (* 86400 26)) (< time (* 86400 27))) (consDate 27 7 2016)
  (ite (and (>= time (* 86400 27)) (< time (* 86400 28))) (consDate 28 7 2016)
  (ite (and (>= time (* 86400 28)) (< time (* 86400 29))) (consDate 29 7 2016)
  (ite (and (>= time (* 86400 29)) (< time (* 86400 30))) (consDate 30 7 2016)
  (ite (and (>= time (* 86400 30)) (< time (* 86400 31))) (consDate 31 7 2016)
  undefDate
  )))))))))))))))))))))))))))))))
)

(declare-fun state (Int) State)

(declare-fun CreditTransfer_id (CreditTransfer) Int) 
(declare-fun CreditTransfer_orderingAccount (CreditTransfer) IBAN)
(declare-fun CreditTransfer_beneficiaryAccount (CreditTransfer) IBAN)
(declare-fun CreditTransfer_requestedExecutionDate (CreditTransfer) Date)
(declare-fun CreditTransfer_actualExecutionDate (CreditTransfer) Date)
(declare-fun CreditTransfer_receivedTime (CreditTransfer) Time)
(declare-fun CreditTransfer_amount (CreditTransfer) Money) 

(declare-fun CreditTransfer_create_id (State) Int)
(declare-fun CreditTransfer_create_orderingAccount (State) IBAN)
(declare-fun CreditTransfer_create_beneficiaryAccount (State) IBAN)
(declare-fun CreditTransfer_create_requestedExecutionDate (State) Date)
(declare-fun CreditTransfer_create_amount (State) Money)

(declare-const now Time)

(define-fun valid ((current State) (next State)) Bool
  true      
)

(define-fun CreditTransfer_create ((current State) (next State)) Bool
  (and
    ; Preconditions
    (not (CreditTransfer_initialized (creditTransfer current (CreditTransfer_create_id next))))
    (= (currency (CreditTransfer_create_amount next)) "EUR")
    (> (amount (CreditTransfer_create_amount next)) 0)
    (or 
      (= (countryCode (CreditTransfer_create_orderingAccount next)) "NL")
      (= (countryCode (CreditTransfer_create_orderingAccount next)) "BE")
    )
    (or 
      (= (countryCode (CreditTransfer_create_beneficiaryAccount next)) "NL")
      (= (countryCode (CreditTransfer_create_beneficiaryAccount next)) "BE")
    )
    (= (countryCode (CreditTransfer_create_orderingAccount next)) (countryCode (CreditTransfer_create_beneficiaryAccount next)))
    
    ; Postconditions
    (= (CreditTransfer_id (creditTransfer next (CreditTransfer_create_id next))) (CreditTransfer_create_id next)) 
    (= (CreditTransfer_orderingAccount (creditTransfer next (CreditTransfer_create_id next))) (CreditTransfer_create_orderingAccount next))
    (= (CreditTransfer_beneficiaryAccount (creditTransfer next (CreditTransfer_create_id next))) (CreditTransfer_create_beneficiaryAccount next))
    (= (CreditTransfer_requestedExecutionDate (creditTransfer next (CreditTransfer_create_id next))) (CreditTransfer_create_requestedExecutionDate next))
    (= (CreditTransfer_receivedTime (creditTransfer next (CreditTransfer_create_id next))) now)
    (= (CreditTransfer_amount (creditTransfer next (CreditTransfer_create_id next))) (CreditTransfer_create_amount next))    
  )
)

(declare-const current State)
(declare-const next State)

(assert (= now 1))

; Transition parameter values
(assert (= (CreditTransfer_create_id next) 1))
(assert (= (CreditTransfer_create_orderingAccount next) (consIBAN "NL" 34 "INGB00360457517")))
(assert (= (CreditTransfer_create_beneficiaryAccount next) (consIBAN "NL" 57 "INGB00348013574")))
(assert (= (CreditTransfer_create_requestedExecutionDate next) (consDate 10 7 2016)))
(assert (= (CreditTransfer_create_amount next) (consMoney "EUR" 6000)))

; Current state values
(assert (= (CreditTransfer_initialized (creditTransfer current 1)) false))

; Check the transition
(assert (CreditTransfer_create current next))

(check-sat)

(get-value (
  (CreditTransfer_orderingAccount (creditTransfer next 1))
  (CreditTransfer_beneficiaryAccount (creditTransfer next 1))
))