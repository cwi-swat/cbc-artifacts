
(define-fun noPenalty ( (amount Int)) Int amount)

(declare-datatypes () (  ( OpenAccountParams (consOpenAccountParams  (minimumDeposit Int) (newAccountNr Int) (initialDeposit Int) (toState Int)) (noOpenAccountParams) ) ))
(declare-datatypes () (  ( CloseParams (consCloseParams  (toState Int)) (noCloseParams) ) ))
(declare-datatypes () (  ( WithdrawParams (consWithdrawParams  (amount Int) (toState Int)) (noWithdrawParams) ) ))
(declare-datatypes () (  ( UnblockParams (consUnblockParams  (toState Int)) (noUnblockParams) ) ))
(declare-datatypes () (  ( DepositParams (consDepositParams  (amount Int) (toState Int)) (noDepositParams) ) ))
(declare-datatypes () (  ( BlockParams (consBlockParams  (toState Int)) (noBlockParams) ) ))

(declare-datatypes () (  ( SavingAccount (consSavingAccount  (state Int) (accountNumber Int) (balance Int) (step Int)) (noSavingAccount) ) ))

(declare-datatypes () (  ( State (consState  (savingAccount SavingAccount) (depth Int) (openAccountParams OpenAccountParams) (closeParams CloseParams) (withdrawParams WithdrawParams) (unblockParams UnblockParams) (depositParams DepositParams) (blockParams BlockParams)) ) ))

(define-fun openAccount ( (current State) (next State)) Bool 
  (and 
    (= (depth next) (+ (depth current) 1)) 
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
    (= (depth next) (+ (depth current) 1)) 
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
    (= (depth next) (+ (depth current) 1)) 
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
    (= (depth next) (+ (depth current) 1)) 
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
    (= (depth next) (+ (depth current) 1)) 
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
    (= (depth next) (+ (depth current) 1)) 
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



(declare-const curState State)
(declare-const nextState State)

(assert (= (savingAccount curState) noSavingAccount))

(assert (= (initialDeposit (openAccountParams nextState)) 40))
(assert (= (newAccountNr (openAccountParams nextState)) 123))
(assert (= (toState (openAccountParams nextState)) 1))


(assert (= (blockParams nextState) noBlockParams))
(assert (= (unblockParams nextState) noUnblockParams))
(assert (= (depositParams nextState) noDepositParams))
(assert (= (closeParams nextState) noCloseParams))
(assert (= (withdrawParams curState) noWithdrawParams))


(assert (openAccount curState nextState))

(check-sat)
(get-unsat-core)

(pop 1)

(push 1)
(declare-const curState State)
(declare-const nextState State)

(assert (= (savingAccount curState) noSavingAccount))

(assert (= (blockParams curState) noBlockParams))
(assert (= (unblockParams curState) noUnblockParams))
(assert (= (withdrawParams curState) noWithdrawParams))
(assert (= (depositParams curState) noDepositParams))
(assert (= (closeParams curState) noCloseParams))
(assert (= (openAccountParams curState) noOpenAccountParams))

(assert (= (initialDeposit (openAccountParams nextState)) 999))
;(assert (= (minimumDeposit (openAccountParams nextState)) 50))
(assert (= (newAccountNr (openAccountParams nextState)) 123))
(assert (= (toState (openAccountParams nextState)) 1))

(define-fun balanceUnderZero ((state State)) Bool
    (< (balance (savingAccount state)) 0) 
)

(define-fun balanceOverThousand ((state State)) Bool
  (> (balance (savingAccount state)) 9999)
)

(define-fun errorCondition ((state State)) Bool
  (ite (= (savingAccount state) noSavingAccount)
    false
    (or (balanceUnderZero state) (balanceOverThousand state))
  )
)
