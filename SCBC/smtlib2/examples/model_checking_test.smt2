;(set-option :smt.auto-config false) ; disable automatic self configuration
;(set-option :smt.mbqi false) ; disable model-based quantifier instantiation
;(set-option :produce-unsat-cores true)
;(set-option :model.compact true)
;(set-option :timeout 30000)

(declare-datatypes () ((WithdrawParams (cons (amount Int)) (noWithdraw))))
(declare-datatypes () ((DepositParams (cons (amount Int)) (noDeposit))))

(declare-datatypes () ((SavingAccount (cons (balance Int)) emptySA )))

(declare-datatypes () ((State (cons (savingAccount SavingAccount) 
                                    ;(nrOfSavingAccounts Int) 
                                    (step Int) 
                                    (idx Int) 
                                    (withdrawParams WithdrawParams) 
                                    (depositParams DepositParams)))))

(declare-datatypes () ((StateList nil (cons (head State) (tail StateList)))))

(define-fun notEmpty ((p StateList)) Bool 
  (not (= p nil))
)

(define-fun isEmpty ((p StateList)) Bool
  (= p nil)
)

(define-fun initial ((state State)) Bool
  (and 
    ;(= (nrOfSavingAccounts state) 1)
    ;(forall ((x Int)) (ite (= x 1) (= (balance (select (savingAccounts state) x)) 500) (= (select (savingAccounts state) x) emptySA))) 
    (= (savingAccount state) emptySA)
    (= (step state) 0) 
    (= (idx state) 0) 
    (= (withdrawParams state) noWithdraw) 
    (= (depositParams state) noDeposit)
  )
)

(define-fun openAccount ((cur State) (nex State)) Bool
  (and 
    (= (step nex) 0) 
    (= (idx nex) (+ (idx cur) 1))
    (= (savingAccount cur) emptySA)
    (= (balance (savingAccount nex)) 500)
  )
)

(define-fun withdraw ((cur State) (nex State)) Bool
  (and 
    (= (step nex) 1) 
    (= (idx nex) (+ (idx cur) 1)) 
    (> (amount (withdrawParams nex)) 0) 
    (>= (- (balance (savingAccount cur)) (amount (withdrawParams nex))) 0) 
    (= (balance (savingAccount nex)) (- (balance (savingAccount cur)) (amount (withdrawParams nex))))
    (not (= (savingAccount cur) emptySA))

    ;(= (savingAccounts nex) (store (savingAccounts cur) 1 (select (savingAccounts nex) 1)))
    ;(= (nrOfSavingAccounts nex) (nrOfSavingAccounts cur))
  )
)

(define-fun deposit ((cur State) (nex State)) Bool
	(and (= (step nex) 2)
    (= (idx nex) (+ (idx cur) 1)) 
    (> (amount (depositParams nex)) 0) 
    (<= (+ (balance (savingAccount cur)) (amount (depositParams nex))) 1000)
    (= (balance (savingAccount nex)) (+ (balance (savingAccount cur)) (amount (depositParams nex))))
    (not (= (savingAccount cur) emptySA))

    ;(= (savingAccounts nex) (store (savingAccounts cur) 1 (select (savingAccounts nex) 1)))
    ;(= (balance (select (savingAccounts nex) 1)) (+ (balance (select (savingAccounts cur) 1)) (amount (depositParams nex))))
    ;(= (nrOfSavingAccounts nex) (nrOfSavingAccounts cur))
  )
)

(define-fun balanceUnderZero ((state State)) Bool
  	(< (balance (savingAccount state)) 1) 
)

(define-fun balanceOverThousand ((state State)) Bool
	(> (balance (savingAccount state)) 999)
)

(define-fun transitionCondition ((cur State) (nex State)) Bool
	(and 
    (or 
      (and (openAccount cur nex)
            (= (depositParams nex) noDeposit)
            (= (withdrawParams nex) noWithdraw)
      )
      (and  (withdraw cur nex) 
            (>= (amount (withdrawParams nex)) 10)
            (<= (amount (withdrawParams nex)) 60)
            (= (depositParams nex) noDeposit)
      ) 
      (and  (deposit cur nex)
            (>= (amount (depositParams nex)) 10)
            (<= (amount (depositParams nex)) 60)
            (= (withdrawParams nex) noWithdraw)
      )
    ) 
    (< (idx cur) 10)
  ); (deposit cur nex)) (< (idx cur) 11))  (withdraw cur nex)
) 

(define-fun errorCondition ((state State)) Bool
	(ite (not (= (savingAccount state) emptySA)) 
    (or (balanceUnderZero state) (balanceOverThousand state))
    false
  )
)

(declare-fun checkTransition (StateList) Bool)
 
(assert 
	(forall ((sts StateList))
  	(!	
  		(and (= (isEmpty (tail sts)) (errorCondition (head sts)))
  			(=> (and (notEmpty sts) (notEmpty (tail sts)))	  
          (and (transitionCondition (head sts) (head (tail sts))) (checkTransition (tail sts)))
     		) 
      )
     	:pattern ((checkTransition sts))
  	) 
  ) 
)

(declare-const states StateList)

(assert (and (notEmpty states) (initial (head states)) (checkTransition states)))

(push 1)
(check-sat)

(get-model)
