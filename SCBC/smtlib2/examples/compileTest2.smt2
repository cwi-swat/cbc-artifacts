;(set-option :produce-unsat-cores true)
(set-option :smt.auto-config false) ; disable automatic self configuration
;(set-option :smt.mbqi false) ; disable model-based quantifier instantiation
(set-option :model.compact true)

(define-fun noPenalty ( (amount Int)) Int amount)

(declare-datatypes () (  ( OpenAccountParams (consOpenAccountParams  (minimumDeposit Int) (newAccountNr Int) (initialDeposit Int) (toState Int)) (noOpenAccountParams) ) ))
(declare-datatypes () (  ( CloseParams (consCloseParams  (toState Int)) (noCloseParams) ) ))
(declare-datatypes () (  ( WithdrawParams (consWithdrawParams  (amount Int) (toState Int)) (noWithdrawParams) ) ))
(declare-datatypes () (  ( UnblockParams (consUnblockParams  (toState Int)) (noUnblockParams) ) ))
(declare-datatypes () (  ( DepositParams (consDepositParams  (amount Int) (toState Int)) (noDepositParams) ) ))
(declare-datatypes () (  ( BlockParams (consBlockParams  (toState Int)) (noBlockParams) ) ))

(declare-datatypes () (  ( SavingAccount (consSavingAccount  (state Int) (accountNumber Int) (balance Int) (step Int)) (noSavingAccount) ) ))

(declare-datatypes () (  ( State (consState  (savingAccount SavingAccount) (openAccountParams OpenAccountParams) (closeParams CloseParams) (withdrawParams WithdrawParams) (unblockParams UnblockParams) (depositParams DepositParams) (blockParams BlockParams)) ) ))

(define-fun openAccount ( (current State) (next State)) Bool 
  (and 
    (= (minimumDeposit (openAccountParams next)) 50) 
    (>= (initialDeposit (openAccountParams next)) (minimumDeposit (openAccountParams next)))
    (> (newAccountNr (openAccountParams next)) 0) 
    (= (toState (openAccountParams next)) 1) 
    (= (savingAccount current) noSavingAccount) 
    (= (balance (savingAccount next)) (initialDeposit (openAccountParams next))) 
    (= (accountNumber (savingAccount next)) (newAccountNr (openAccountParams next))) 
    (= (step (savingAccount next)) 3) 
    (not (= (savingAccount next) noSavingAccount)) 
    (= (state (savingAccount next)) (toState (openAccountParams next)))
  )
)

(define-fun close ( (current State) (next State)) Bool 
  (and
    (= (balance (savingAccount current)) 0) 
    (and (= (state (savingAccount current)) 1) (= (toState (closeParams next)) 3)) 
    (not (= (savingAccount current) noSavingAccount)) 
    (= (accountNumber (savingAccount next)) (accountNumber (savingAccount current))) 
    (= (balance (savingAccount next)) (balance (savingAccount current))) 
    (= (step (savingAccount next)) 6) 
    (not (= (savingAccount next) noSavingAccount)) 
    (= (state (savingAccount next)) (toState (closeParams next)))
  )
)

(define-fun withdraw ( (current State) (next State)) Bool 
  (and
    (>= (balance (savingAccount current)) (noPenalty  (amount (withdrawParams next)))) 
    (> (amount (withdrawParams next)) 0) 
    (and (= (state (savingAccount current)) 1) (= (toState (withdrawParams next)) 1)) 
    (not (= (savingAccount current) noSavingAccount)) 
    (= (balance (savingAccount next)) (- (balance (savingAccount current)) (noPenalty  (amount (withdrawParams next))))) 
    (= (accountNumber (savingAccount next)) (accountNumber (savingAccount current))) 
    (= (step (savingAccount next)) 4) 
    (not (= (savingAccount next) noSavingAccount)) 
    (= (state (savingAccount next)) (toState (withdrawParams next)))
  )
)

(define-fun unblock ( (current State) (next State)) Bool 
  (and 
    (and (= (state (savingAccount current)) 2) (= (toState (unblockParams next)) 1)) 
    (not (= (savingAccount current) noSavingAccount)) 
    (= (accountNumber (savingAccount next)) (accountNumber (savingAccount current))) 
    (= (balance (savingAccount next)) (balance (savingAccount current))) 
    (= (step (savingAccount next)) 5) 
    (not (= (savingAccount next) noSavingAccount)) 
    (= (state (savingAccount next)) (toState (unblockParams next)))
  )
)

(define-fun deposit ( (current State) (next State)) Bool 
  (and
    (> (noPenalty  (amount (depositParams next))) 0) 
    (and (= (state (savingAccount current)) 1) (= (toState (depositParams next)) 1)) 
    (not (= (savingAccount current) noSavingAccount)) 
    (= (balance (savingAccount next)) (+ (balance (savingAccount current)) (noPenalty  (amount (depositParams next))))) 
    (= (accountNumber (savingAccount next)) (accountNumber (savingAccount current))) 
    (= (step (savingAccount next)) 1) 
    (not (= (savingAccount next) noSavingAccount)) 
    (= (state (savingAccount next)) (toState (depositParams next)))
  )
)

(define-fun block ( (current State) (next State)) Bool 
  (and
    (and (= (state (savingAccount current)) 1) (= (toState (blockParams next)) 2)) 
    (not (= (savingAccount current) noSavingAccount)) 
    (= (accountNumber (savingAccount next)) (accountNumber (savingAccount current))) 
    (= (balance (savingAccount next)) (balance (savingAccount current))) 
    (= (step (savingAccount next)) 2) 
    (not (= (savingAccount next) noSavingAccount)) 
    (= (state (savingAccount next)) (toState (blockParams next)))
  )
)

(push 1)

(define-fun initial ((state State)) Bool
  (and 
    (= (savingAccount state) noSavingAccount)

    (= (withdrawParams state) noWithdrawParams) 
    (= (depositParams state) noDepositParams)
    (= (blockParams state) noBlockParams)
    (= (unblockParams state) noUnblockParams)
    (= (closeParams state) noCloseParams)
    (= (openAccountParams state) noOpenAccountParams)
  )
)

(define-fun transitionCondition ((cur State) (nex State)) Bool
    (or 
      (and  (block cur nex) 
            (= (unblockParams nex) noUnblockParams)
            (= (openAccountParams nex) noOpenAccountParams)
            (= (depositParams nex) noDepositParams)
            (= (closeParams nex) noCloseParams)
            (= (withdrawParams nex) noWithdrawParams)
      ) 

      (and  (unblock cur nex) 
      		  (= (blockParams nex) noBlockParams)
            (= (openAccountParams nex) noOpenAccountParams)
            (= (depositParams nex) noDepositParams)
            (= (closeParams nex) noCloseParams)
            (= (withdrawParams nex) noWithdrawParams)
      )

      (and  (openAccount cur nex) 
      		(= (blockParams nex) noBlockParams)
            (= (unblockParams nex) noUnblockParams)
            (= (depositParams nex) noDepositParams)
            (= (closeParams nex) noCloseParams)
            (= (withdrawParams nex) noWithdrawParams)

            (>= (initialDeposit (openAccountParams nex)) 10)
            (<= (initialDeposit (openAccountParams nex)) 100)
      ) 

      (and  (deposit cur nex) 
      		(= (blockParams nex) noBlockParams)
            (= (unblockParams nex) noUnblockParams)
            (= (openAccountParams nex) noOpenAccountParams)
            (= (closeParams nex) noCloseParams)
            (= (withdrawParams nex) noWithdrawParams)

            (>= (amount (depositParams nex)) 10)
            (<= (amount (depositParams nex)) 100)
      ) 

      (and  (close cur nex) 
      		(= (blockParams nex) noBlockParams)
            (= (unblockParams nex) noUnblockParams)
            (= (openAccountParams nex) noOpenAccountParams)
            (= (depositParams nex) noDepositParams)
            (= (withdrawParams nex) noWithdrawParams)
      ) 

      (and  (withdraw cur nex) 
      		(= (blockParams nex) noBlockParams)
            (= (unblockParams nex) noUnblockParams)
            (= (openAccountParams nex) noOpenAccountParams)
            (= (depositParams nex) noDepositParams)
            (= (closeParams nex) noCloseParams)

            (>= (amount (withdrawParams nex)) 10)
            (<= (amount (withdrawParams nex)) 100)            
      ) 
    ) 
) 

(define-fun balanceUnderZero ((state State)) Bool
  	(< (balance (savingAccount state)) 0) 
)

(define-fun balanceOverThousand ((state State)) Bool
	(> (balance (savingAccount state)) 999)
)

(define-fun accountIsClosed ((st State)) Bool
  (= (state (savingAccount st)) 3)
)

(define-fun errorCondition ((state State)) Bool
	(or (balanceUnderZero state) (balanceOverThousand state))
)

(declare-const s1 State)
(declare-const s2 State)
(declare-const s3 State)
(declare-const s4 State)
(declare-const s5 State)
(declare-const s6 State)
(declare-const s7 State)
(declare-const s8 State)
(declare-const s9 State)
(declare-const s10 State)
(declare-const s11 State)
(declare-const s12 State)
(declare-const s13 State)
(declare-const s14 State)
(declare-const s15 State)
(declare-const s16 State)
(declare-const s17 State)
(declare-const s18 State)
(declare-const s19 State)
(declare-const s20 State)
(declare-const s21 State)
(declare-const s22 State)
(declare-const s23 State)
(declare-const s24 State)
(declare-const s25 State)
(declare-const s26 State)
(declare-const s27 State)
(declare-const s28 State)
(declare-const s29 State)
(declare-const s30 State)
(declare-const s31 State)

(assert 
  (and
    (initial s1)
    (transitionCondition s1 s2) (not (errorCondition s2))
    (transitionCondition s2 s3) (not (errorCondition s3))
    (transitionCondition s3 s4) (not (errorCondition s4))
    (transitionCondition s4 s5) (not (errorCondition s5))
    (transitionCondition s5 s6) (not (errorCondition s6))
    (transitionCondition s6 s7) (not (errorCondition s7))
    (transitionCondition s7 s8) (not (errorCondition s8))
    (transitionCondition s8 s9) (not (errorCondition s9))
    (transitionCondition s9 s10) (not (errorCondition s10))
    (transitionCondition s10 s11) (not (errorCondition s11))
    (transitionCondition s11 s12) (not (errorCondition s12))
    (transitionCondition s12 s13) (not (errorCondition s13))
    (transitionCondition s13 s14) (not (errorCondition s14))
    (transitionCondition s14 s15) (not (errorCondition s15))
    (transitionCondition s15 s16) (not (errorCondition s16))
    (transitionCondition s16 s17) (not (errorCondition s17))
    (transitionCondition s17 s18) (not (errorCondition s18))
    (transitionCondition s18 s19) (not (errorCondition s19))
    (transitionCondition s19 s20) (not (errorCondition s20))
    (transitionCondition s20 s21) (not (errorCondition s21))
    (transitionCondition s21 s22) (not (errorCondition s22))
    (transitionCondition s22 s23) (not (errorCondition s23))
    (transitionCondition s23 s24) (not (errorCondition s24))
    (transitionCondition s24 s25) (not (errorCondition s25))
    (transitionCondition s25 s26) (not (errorCondition s26))
    (transitionCondition s26 s27) (not (errorCondition s27))
    (transitionCondition s27 s28) (not (errorCondition s28))
    (transitionCondition s28 s29) (not (errorCondition s29))
    (transitionCondition s29 s30) (not (errorCondition s30))

    ;(transitionCondition s25 s26) (errorCondition s26)
    (transitionCondition s30 s31) (errorCondition s31)
    ;(transitionCondition s20 s21) (errorCondition s21)
  )
)

(check-sat)
(get-model)

(pop 1)
