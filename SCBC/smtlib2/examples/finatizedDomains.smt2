(set-option :print-success true)

(declare-sort State)

(declare-sort Money)
(declare-sort IBAN)

(declare-sort SavingAccount)

(declare-fun initialized (SavingAccount) Bool)
(declare-fun balance (SavingAccount) Money)
(declare-fun id (SavingAccount) IBAN) 
(declare-fun savingAccount (State IBAN) SavingAccount) 

(declare-fun step (State) Int)

(declare-fun initialDepositParam (State) Money)
(declare-fun newAccountIbanParam (State) IBAN)

(declare-fun amountParam (State) Money)
(declare-fun accountIbanParam (State) IBAN)

(declare-fun intVal (Money) Int)

(declare-const IBAN0 IBAN)
(declare-const IBAN1 IBAN)

(define-fun openAccount ((current State) (next State)) Bool
	(and
		(not (initialized (savingAccount current (newAccountIbanParam next))))
		(initialized (savingAccount next (newAccountIbanParam next)))
		(> (intVal (initialDepositParam next)) 10)
		(= (intVal (balance (savingAccount next (newAccountIbanParam next)))) (intVal (initialDepositParam next)))
		(= (id (savingAccount next (newAccountIbanParam next))) (newAccountIbanParam next))
		(xor (= (newAccountIbanParam next) IBAN0) (= (newAccountIbanParam next) IBAN1))
		(= (step next) 0)
		
		; Frame conditions
		(=> (not (= (newAccountIbanParam next) IBAN0)) 
			(and 
				(= (initialized (savingAccount current IBAN0)) (initialized (savingAccount next IBAN0)))
				(= (id (savingAccount current IBAN0)) (id (savingAccount next IBAN0)))
				(= (balance (savingAccount current IBAN0)) (balance (savingAccount next IBAN0)))
			)
		)
		(=> (not (= (newAccountIbanParam next) IBAN1)) 
			(and 
				(= (initialized (savingAccount current IBAN1)) (initialized (savingAccount next IBAN1)))
				(= (id (savingAccount current IBAN1)) (id (savingAccount next IBAN1)))
				(= (balance (savingAccount current IBAN1)) (balance (savingAccount next IBAN1)))
			)
		)		
		
	)
)

(define-fun withdraw ((current State) (next State)) Bool
	(and
		(initialized (savingAccount current (accountIbanParam next)))
		(initialized (savingAccount next (accountIbanParam next)))
		(= (id (savingAccount next (accountIbanParam next))) (id (savingAccount current (accountIbanParam next))))
		(and (> (intVal (amountParam next)) 0) (< (intVal (amountParam next)) 7))
		;(> (- (intVal (balance (savingAccount current))) (intVal (amountParam next))) 0)
		(= (intVal (balance (savingAccount next (accountIbanParam next)))) (- (intVal (balance (savingAccount current (accountIbanParam next)))) (intVal (amountParam next))))
		(= (step next) 1)
		
		; Frame conditions
		(=> (not (= (accountIbanParam next) IBAN0)) 
			(and 
				(= (initialized (savingAccount current IBAN0)) (initialized (savingAccount next IBAN0)))
				(= (id (savingAccount current IBAN0)) (id (savingAccount next IBAN0)))
				(= (balance (savingAccount current IBAN0)) (balance (savingAccount next IBAN0)))
			)
		)
		(=> (not (= (accountIbanParam next) IBAN1)) 
			(and 
				(= (initialized (savingAccount current IBAN1)) (initialized (savingAccount next IBAN1)))
				(= (id (savingAccount current IBAN1)) (id (savingAccount next IBAN1)))
				(= (balance (savingAccount current IBAN1)) (balance (savingAccount next IBAN1)))
			)
		)		
	)  
)

(define-fun mustBePositive ((st State)) Bool
	(and
		(=> (initialized (savingAccount st IBAN0)) (> (intVal (balance (savingAccount st IBAN0))) 0))
		(=> (initialized (savingAccount st IBAN1)) (> (intVal (balance (savingAccount st IBAN1))) 0))
	)	
)

(define-fun initial ((st State)) Bool
	(and
		(not (initialized (savingAccount st IBAN0)))
		(not (initialized (savingAccount st IBAN1)))
	)
)

(define-fun transition ((current State) (next State)) Bool
	(or 
		(openAccount current next)
		(withdraw current next)
	)
) 

(define-fun errorCondition ((st State)) Bool
	(and
		(not (mustBePositive st))
		(initialized (savingAccount st IBAN0))
		(initialized (savingAccount st IBAN1))
	)
)

(declare-const S0 State)
(declare-const S1 State)
(declare-const S2 State)
(declare-const S3 State)
(declare-const S4 State)

(declare-const SA0 SavingAccount)
(declare-const SA1 SavingAccount)
(declare-const SA2 SavingAccount)
(declare-const SA3 SavingAccount)

(declare-const M0 Money)
(declare-const M1 Money)
(declare-const M2 Money)
(declare-const M3 Money)

;(assert (or (= (savingAccount S0) SA0) (= (savingAccount S0) SA1) (= (savingAccount S0) SA2) (= (savingAccount S0) SA3)))
;(assert (or (= (savingAccount S1) SA0) (= (savingAccount S1) SA1) (= (savingAccount S1) SA2) (= (savingAccount S1) SA3)))
;(assert (or (= (savingAccount S2) SA0) (= (savingAccount S2) SA1) (= (savingAccount S2) SA2) (= (savingAccount S2) SA3)))
;(assert (or (= (savingAccount S3) SA0) (= (savingAccount S3) SA1) (= (savingAccount S3) SA2) (= (savingAccount S3) SA3)))

;(assert (xor (= (balance SA0) M0) (= (balance SA0) M1) (= (balance SA0) M2) (= (balance SA0) M3)))
;(assert (xor (= (balance SA1) M0) (= (balance SA1) M1) (= (balance SA1) M2) (= (balance SA1) M3)))
;(assert (xor (= (balance SA2) M0) (= (balance SA2) M1) (= (balance SA2) M2) (= (balance SA2) M3)))
;(assert (xor (= (balance SA3) M0) (= (balance SA3) M1) (= (balance SA3) M2) (= (balance SA3) M3)))

;(assert (= (id SA0) IBAN))
;(assert (or (= (id SA1) IBAN0) (= (id SA1) IBAN1) (= (id SA1) IBAN2) (= (id SA1) IBAN3)))
;(assert (or (= (id SA2) IBAN0) (= (id SA2) IBAN1) (= (id SA2) IBAN2) (= (id SA2) IBAN3)))
;(assert (or (= (id SA3) IBAN0) (= (id SA3) IBAN1) (= (id SA3) IBAN2) (= (id SA3) IBAN3)))

(assert (and (initial S0) 		(not (errorCondition S0))))
(assert (and (transition S0 S1) (not (errorCondition S1))))
(assert (and (transition S1 S2) (not (errorCondition S2))))
(assert (and (transition S2 S3) (not (errorCondition S3))))
(assert (and (transition S3 S4) (errorCondition S4)))

(check-sat)

(get-model)
