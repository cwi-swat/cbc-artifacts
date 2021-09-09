(set-option :produce-unsat-cores true)

(define-fun singleInterest ( (balance Int) (interest Int)) Int (* (div balance 100) interest))

(declare-datatypes () (  ( OpenAccountParams (consOpenAccountParams  (minimalDeposit Int) (accountNr Int) (initialDeposit Int) (_toState Int)) (noOpenAccountParams) ) ))
(declare-datatypes () (  ( FixedTermSavingsAccount (consFixedTermSavingsAccount  (accountNumber Int) (balance Int) (_step Int) (_state Int)) (noFixedTermSavingsAccount) ) ))
(declare-datatypes () (  ( State (consState  (fixedTermSavingsAccount FixedTermSavingsAccount) (openAccountParams OpenAccountParams)) ) ))

(define-fun positiveBalance ( (state State)) Bool (>= (balance (fixedTermSavingsAccount state)) 0))

(declare-const current State)
(declare-const next State)

(assert (= (fixedTermSavingsAccount current) noFixedTermSavingsAccount))
(assert (= (minimalDeposit (openAccountParams next)) 5000))
(assert (= (accountNr (openAccountParams next)) 123))
(assert (= (initialDeposit (openAccountParams next)) 5100))
(assert (not (= (openAccountParams next) noOpenAccountParams)))
(assert (! (>= (initialDeposit (openAccountParams next)) (minimalDeposit (openAccountParams next))) :named |_project://rebel/example/account/AccountLib.ebl_[232,32,$11,2%,$11,34%]|))
(assert (= (_toState (openAccountParams next)) 4))
;(assert (not (= (fixedTermSavingsAccount current) noFixedTermSavingsAccount)))
(assert (! (= (balance (fixedTermSavingsAccount next)) (initialDeposit (openAccountParams next))) :named |_project://rebel/example/account/AccountLib.ebl_[290,34,$14,2%,$14,36%]|))
(assert (! (= (accountNumber (fixedTermSavingsAccount next)) (accountNr (openAccountParams next))) :named |_project://rebel/example/account/AccountLib.ebl_[328,35,$15,2%,$15,37%]|))
(assert (= (_step (fixedTermSavingsAccount next)) 3))
(assert (not (= (fixedTermSavingsAccount next) noFixedTermSavingsAccount)))
(assert (= (_state (fixedTermSavingsAccount next)) (_toState (openAccountParams next))))

(check-sat)
(get-unsat-core)