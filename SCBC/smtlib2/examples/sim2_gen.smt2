(set-option :produce-unsat-cores true)
(define-sort Percentage () Int)
(define-sort Frequency () Int)
(define-sort Currency () String)
(define-sort Term () Int)
(define-sort Period () Int)

(declare-datatypes () (  ( IBAN (consIBAN  (countryCode String) (checksum Int) (accountNumber String)) ) ))
(declare-datatypes () (  ( Money (consMoney  (currency String) (amount Int)) ) ))
(declare-datatypes () (  ( Date (consDate  (date Int) (month Int) (year Int)) (undefDate) ) ))
(declare-datatypes () (  ( Time (consTime  (hour Int) (minutes Int) (seconds Int)) (undefTime) ) ))
(declare-datatypes () (  ( DateTime (consDateTime  (date Date) (time Time)) (undefDateTime) ) ))

(declare-sort State)
(declare-sort simple_transaction.Account)
(declare-sort simple_transaction.Transaction)

(declare-fun field_simple_transaction.Account__state ( simple_transaction.Account) Int)
(declare-fun field_simple_transaction.Account_balance ( simple_transaction.Account) Money)
(declare-fun field_simple_transaction.Account__step ( simple_transaction.Account) Int)
(declare-fun field_simple_transaction.Account_accountNumber ( simple_transaction.Account) IBAN)

(declare-fun field_simple_transaction.Transaction_to ( simple_transaction.Transaction) IBAN)
(declare-fun field_simple_transaction.Transaction_amount ( simple_transaction.Transaction) Money)
(declare-fun field_simple_transaction.Transaction__state ( simple_transaction.Transaction) Int)
(declare-fun field_simple_transaction.Transaction_createdOn ( simple_transaction.Transaction) DateTime)
(declare-fun field_simple_transaction.Transaction_from ( simple_transaction.Transaction) IBAN)
(declare-fun field_simple_transaction.Transaction_id ( simple_transaction.Transaction) Int)
(declare-fun field_simple_transaction.Transaction__step ( simple_transaction.Transaction) Int)
(declare-fun field_simple_transaction.Transaction_bookedOn ( simple_transaction.Transaction) Date)

(declare-fun eventParam_simple_transaction.Transaction_start__toState ( State) Int)
(declare-fun eventParam_simple_transaction.Transaction_start_amount ( State) Money)
(declare-fun eventParam_simple_transaction.Transaction_start__id ( State) Int)
(declare-fun eventParam_simple_transaction.Transaction_start_from ( State) IBAN)
(declare-fun eventParam_simple_transaction.Transaction_start_to ( State) IBAN)
(declare-fun eventParam_simple_transaction.Transaction_start_bookOn ( State) Date)

(declare-fun spec_simple_transaction.Account ( State IBAN) simple_transaction.Account)
(define-fun spec_simple_transaction.Account_initialized ( (entity simple_transaction.Account)) Bool (or (= (field_simple_transaction.Account__state  entity) 1) (= (field_simple_transaction.Account__state  entity) 3) (= (field_simple_transaction.Account__state  entity) 2)))

(define-fun spec_simple_transaction.Account_frame ((curEntity simple_transaction.Account) (nextEntity simple_transaction.Account)) Bool
    (and (= (field_simple_transaction.Account__state nextEntity) (field_simple_transaction.Account__state curEntity))
         (= (field_simple_transaction.Account_balance nextEntity) (field_simple_transaction.Account_balance curEntity))
         (= (field_simple_transaction.Account__step nextEntity) (field_simple_transaction.Account__step curEntity))
         (= (field_simple_transaction.Account_accountNumber nextEntity) (field_simple_transaction.Account_accountNumber curEntity))
    )
)

(declare-fun spec_simple_transaction.Transaction ( State Int) simple_transaction.Transaction)
(define-fun spec_simple_transaction.Transaction_initialized ( (entity simple_transaction.Transaction)) Bool (or (= (field_simple_transaction.Transaction__state  entity) 3) (= (field_simple_transaction.Transaction__state  entity) 2) (= (field_simple_transaction.Transaction__state  entity) 4)))

(declare-const current State)
(declare-const next State)

(declare-fun now ( State) DateTime)

(assert (= (now  next) (consDateTime (consDate 26 9 2016) (consTime 4 2 0))))

(assert (= (field_simple_transaction.Transaction__state  (spec_simple_transaction.Transaction  current 1)) 1))
(assert (= (field_simple_transaction.Transaction_id  (spec_simple_transaction.Transaction  current 1)) 1))

(assert (= (field_simple_transaction.Account__state  (spec_simple_transaction.Account  current (consIBAN "NL" 1 "INGB0000001"))) 2))
(assert (= (field_simple_transaction.Account_accountNumber  (spec_simple_transaction.Account  current (consIBAN "NL" 1 "INGB0000001"))) (consIBAN "NL" 1 "INGB0000001")))
(assert (= (field_simple_transaction.Account_balance  (spec_simple_transaction.Account  current (consIBAN "NL" 1 "INGB0000001"))) (consMoney "EUR" 4000)))
(assert (= (field_simple_transaction.Account__state  (spec_simple_transaction.Account  current (consIBAN "NL" 1 "INGB0000002"))) 2))
(assert (= (field_simple_transaction.Account_accountNumber  (spec_simple_transaction.Account  current (consIBAN "NL" 1 "INGB0000002"))) (consIBAN "NL" 1 "INGB0000002")))
(assert (= (field_simple_transaction.Account_balance  (spec_simple_transaction.Account  current (consIBAN "NL" 1 "INGB0000002"))) (consMoney "EUR" 2000)))

(assert (= (eventParam_simple_transaction.Transaction_start__toState  next) 4))
(assert (= (eventParam_simple_transaction.Transaction_start_amount  next) (consMoney "EUR" 3000)))
(assert (= (eventParam_simple_transaction.Transaction_start__id  next) 1))
(assert (= (eventParam_simple_transaction.Transaction_start_from  next) (consIBAN "NL" 1 "INGB0000001")))
(assert (= (eventParam_simple_transaction.Transaction_start_to  next) (consIBAN "NL" 1 "INGB0000002")))
(assert (= (eventParam_simple_transaction.Transaction_start_bookOn  next) (consDate 30 9 2016)))

(define-fun func_singleInterest ( (param_balance Money) (param_interest Percentage)) Money (consMoney  (currency  (consMoney  (currency  param_balance) (* (amount  param_balance)  param_interest))) (div (amount  (consMoney  (currency  param_balance) (* (amount  param_balance)  param_interest)))  100)))

(define-fun event_simple_transaction.Transaction_start ( (current State) (next State) (param_amount Money) (param_from IBAN) (param_to IBAN) (param_bookOn Date) (param__toState Int) (param__id Int)) Bool (and (spec_simple_transaction.Account_initialized  (spec_simple_transaction.Account  current param_from)) (spec_simple_transaction.Account_initialized  (spec_simple_transaction.Account  current param_to)) (not (= param_to param_from)) (> (amount  param_amount) (amount  (consMoney "EUR" 0))) (and (= (field_simple_transaction.Transaction__state  (spec_simple_transaction.Transaction  current param__id)) 1) (= param__toState 4)) (= (field_simple_transaction.Transaction_amount  (spec_simple_transaction.Transaction  next param__id)) param_amount) (= (field_simple_transaction.Transaction_from  (spec_simple_transaction.Transaction  next param__id)) param_from) (= (field_simple_transaction.Transaction_to  (spec_simple_transaction.Transaction  next param__id)) param_to) (= (field_simple_transaction.Transaction_createdOn  (spec_simple_transaction.Transaction  next param__id)) (now  next)) (= (field_simple_transaction.Transaction_bookedOn  (spec_simple_transaction.Transaction  next param__id)) param_bookOn) (= (field_simple_transaction.Transaction_id  (spec_simple_transaction.Transaction  next param__id)) (field_simple_transaction.Transaction_id  (spec_simple_transaction.Transaction  current param__id))) (= (field_simple_transaction.Transaction__step  (spec_simple_transaction.Transaction  next param__id)) 1) (= (field_simple_transaction.Transaction__state  (spec_simple_transaction.Transaction  next param__id)) param__toState)))

(assert (! (spec_simple_transaction.Account_initialized  (spec_simple_transaction.Account  current (eventParam_simple_transaction.Transaction_start_from  next)))  :named |_project://rebel-core/examples/simple_transaction/Library.ebl_[1612,59,$86,2%,$87,28%]|))
(assert (! (spec_simple_transaction.Account_initialized  (spec_simple_transaction.Account  current (eventParam_simple_transaction.Transaction_start_to  next)))  :named |_project://rebel-core/examples/simple_transaction/Library.ebl_[1674,55,$88,2%,$89,26%]|))
(assert (! (not (= (eventParam_simple_transaction.Transaction_start_to  next) (eventParam_simple_transaction.Transaction_start_from  next)))  :named |_project://rebel-core/examples/simple_transaction/Library.ebl_[1735,53,$91,2%,$92,13%]|))
(assert (! (> (amount  (eventParam_simple_transaction.Transaction_start_amount  next)) (amount  (consMoney "EUR" 0)))  :named |_project://rebel-core/examples/simple_transaction/Library.ebl_[1794,18,$94,2%,$94,20%]|))
(assert (! (and (= (field_simple_transaction.Transaction__state  (spec_simple_transaction.Transaction  current (eventParam_simple_transaction.Transaction_start__id  next))) 1) (= (eventParam_simple_transaction.Transaction_start__toState  next) 4))  :named |_project://rebel-core/src/lang/Normalizer.rsc_[0,36,$1,0%,$1,36%]|))
(assert (! (= (field_simple_transaction.Transaction_amount  (spec_simple_transaction.Transaction  next (eventParam_simple_transaction.Transaction_start__id  next))) (eventParam_simple_transaction.Transaction_start_amount  next))  :named |_project://rebel-core/examples/simple_transaction/Library.ebl_[1836,26,$97,2%,$97,28%]|))
(assert (! (= (field_simple_transaction.Transaction_from  (spec_simple_transaction.Transaction  next (eventParam_simple_transaction.Transaction_start__id  next))) (eventParam_simple_transaction.Transaction_start_from  next))  :named |_project://rebel-core/examples/simple_transaction/Library.ebl_[1865,22,$98,2%,$98,24%]|))
(assert (! (= (field_simple_transaction.Transaction_to  (spec_simple_transaction.Transaction  next (eventParam_simple_transaction.Transaction_start__id  next))) (eventParam_simple_transaction.Transaction_start_to  next))  :named |_project://rebel-core/examples/simple_transaction/Library.ebl_[1890,18,$99,2%,$99,20%]|))
(assert (! (= (field_simple_transaction.Transaction_createdOn  (spec_simple_transaction.Transaction  next (eventParam_simple_transaction.Transaction_start__id  next))) (now  next))  :named |_project://rebel-core/examples/simple_transaction/Library.ebl_[1914,81,$101,2%,$102,28%]|))
(assert (! (= (field_simple_transaction.Transaction_bookedOn  (spec_simple_transaction.Transaction  next (eventParam_simple_transaction.Transaction_start__id  next))) (eventParam_simple_transaction.Transaction_start_bookOn  next))  :named |_project://rebel-core/examples/simple_transaction/Library.ebl_[2001,28,$104,2%,$104,30%]|))
(assert (= (field_simple_transaction.Transaction_id  (spec_simple_transaction.Transaction  next (eventParam_simple_transaction.Transaction_start__id  next))) (field_simple_transaction.Transaction_id  (spec_simple_transaction.Transaction  current (eventParam_simple_transaction.Transaction_start__id  next)))))
(assert (! (= (field_simple_transaction.Transaction__step  (spec_simple_transaction.Transaction  next (eventParam_simple_transaction.Transaction_start__id  next))) 1)  :named |_project://rebel-core/src/lang/Normalizer.rsc_[16455,34]|))
(assert (! (= (field_simple_transaction.Transaction__state  (spec_simple_transaction.Transaction  next (eventParam_simple_transaction.Transaction_start__id  next))) (eventParam_simple_transaction.Transaction_start__toState  next))  :named |_project://rebel-core/src/lang/Normalizer.rsc_[0,28,$1,0%,$1,28%]|))

; make sure that the other entities do not change
(assert (spec_simple_transaction.Account_frame (spec_simple_transaction.Account current (consIBAN "NL" 1 "INGB0000001")) (spec_simple_transaction.Account next (consIBAN "NL" 1 "INGB0000001"))))
(assert (spec_simple_transaction.Account_frame (spec_simple_transaction.Account current (consIBAN "NL" 1 "INGB0000002")) (spec_simple_transaction.Account next (consIBAN "NL" 1 "INGB0000002"))))

(check-sat)

(get-value ( (field_simple_transaction.Transaction__state  (spec_simple_transaction.Transaction  next 1))))
(get-value ( (field_simple_transaction.Transaction_id  (spec_simple_transaction.Transaction  next 1))))
(get-value ( (field_simple_transaction.Transaction_amount  (spec_simple_transaction.Transaction  next 1))))
(get-value ( (field_simple_transaction.Transaction_createdOn  (spec_simple_transaction.Transaction  next 1))))
(get-value ( (field_simple_transaction.Transaction_bookedOn  (spec_simple_transaction.Transaction  next 1))))
(get-value ( (field_simple_transaction.Account__state  (spec_simple_transaction.Account  next (consIBAN "NL" 1 "INGB0000001")))))
(get-value ( (field_simple_transaction.Account_accountNumber  (spec_simple_transaction.Account  next (consIBAN "NL" 1 "INGB0000001")))))
(get-value ( (field_simple_transaction.Account_balance  (spec_simple_transaction.Account  next (consIBAN "NL" 1 "INGB0000001")))))
(get-value ( (field_simple_transaction.Account__state  (spec_simple_transaction.Account  next (consIBAN "NL" 1 "INGB0000002")))))
(get-value ( (field_simple_transaction.Account_accountNumber  (spec_simple_transaction.Account  next (consIBAN "NL" 1 "INGB0000002")))))
(get-value ( (field_simple_transaction.Account_balance  (spec_simple_transaction.Account  next (consIBAN "NL" 1 "INGB0000002")))))
