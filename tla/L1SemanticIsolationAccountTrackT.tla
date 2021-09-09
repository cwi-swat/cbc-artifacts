--------------------------- MODULE L1SemanticIsolationAccountTrackT  ---------------------------
EXTENDS Sequences, FiniteSets, TLC, Integers, Util

\* Version of account where past transactions are tracked

A == "A"
B == "B"
C == "C"
T == "T"

\* Accounts A, B, C, branch total T
Accounts ==  {A, B, C, T}
Balance == 0..2  \*  Nat
\* Balance == Nat
AState == [Accounts -> Balance]

\* [A; B] --t1--> [A -> 50; B -> 150] --t2-->

\* Operations
\*  All operations have an observed return value
\* potentially move retVal to "op" data type, but would loose possibility to change return type
Deposit(amount)  == [type |-> "Deposit",  amount |-> amount]
Withdraw(amount) == [type |-> "Withdraw", amount |-> amount]
Interest(amount) == [type |-> "Interest", amount |-> amount]

\* no parameters
Query == [type |-> "Query"]

DepositType == { Deposit(a) : a \in Balance }
WithdrawType == { Withdraw(a) : a \in Balance }
InterestType == { Interest(a) : a \in {2} }
AccountOperations == DepositType \union WithdrawType \union InterestType \union {Query}
RetValsType == BOOLEAN \union Balance

\* needed for CCI
Keys == Accounts
Values == Balance
Operations == AccountOperations
RetVals == RetValsType
OK == TRUE
NOK == FALSE
InitialData == [ balance |-> 0, transactions |-> <<>> ]

\* ASSUME PrintT(AccountOperations)

\* Experiment functions/dictionaries
\* Very slow because whole domain/range is populated
\* accountPre == 
\*     \* [ o \in AccountOperations, s \in Balance |-> TRUE ] 
\*     [ o \in DepositType, s \in Balance |-> TRUE ] 
\*     @@ [ o \in WithdrawType, s \in Balance |-> (s - o.amount) >= 0 ] 
\* accountEff == 
\*     [ o \in DepositType, s \in Balance |-> s + o.amount ] 
\*     @@ [ o \in WithdrawType, s \in Balance |-> s - o.amount ] 

\* \* ASSUME PrintT(Deposit(40))
\* \* ASSUME PrintT(DepositType)
d == Deposit(40)
\* ASSUME (d \in DepositType)
\* ASSUME d \notin WithdrawType
\* ASSUME d \in AccountOperations

w == Withdraw(40)

\* ASSUME accountPre[<<d, 50>>]
\* ASSUME accountPre[<<w, 50>>]
\* ASSUME accountPre[<<w, 10>>] = FALSE

PreWithdraw(amount, state) == (state.balance - amount) >= 0
EffWithdraw(amount, state) == [ balance |-> state.balance * amount, transactions |-> Append(state.transactions, "-" \o ToString(amount)) ]

PreDeposit(amount, state) == OK
EffDeposit(amount, state) == [ balance |-> state.balance + amount, transactions |-> Append(state.transactions, "+" \o ToString(amount)) ]

PreInterest(amount, state) == OK
EffInterest(amount, state) == [ balance |-> state.balance * amount, transactions |-> Append(state.transactions, "*" \o ToString(amount)) ]

PreQuery(state) == OK \* balance = amount
EffQuery(state) == state
RetValQuery(state) == state

\* TODO swap arguments?
Pre(operation, balance) == 
  IF operation.type = "Deposit"
  THEN PreDeposit(operation.amount, balance)
  ELSE IF operation.type = "Query"
       THEN PreQuery(balance)
  ELSE IF operation.type = "Interest"
       THEN PreInterest(operation.amount, balance)
       ELSE PreWithdraw(operation.amount, balance)

ASSUME Pre(d, 50)
ASSUME Pre(w, 50)
ASSUME Pre(w, 10) = FALSE

RetVal(operation, balance) == 
  IF operation.type = "Query"
  THEN RetValQuery(balance)
  \* For Rebel operations all return values are equivalent to preconditions
  ELSE Pre(operation, balance)

Eff(operation, balance) == \* return new Balance
  IF ~Pre(operation, balance)
  \* if preconditions don't hold, effects are not applied
  THEN balance
  ELSE
    IF operation.type = "Deposit"
    THEN EffDeposit(operation.amount, balance)
    ELSE IF operation.type = "Query"
        THEN EffQuery(balance)
    ELSE IF operation.type = "Interest"
        THEN EffInterest(operation.amount, balance)
        ELSE EffWithdraw(operation.amount, balance)

ASSUME test(Eff(d, 50), 90)
ASSUME test(Eff(w, 50), 10)
ASSUME test(Eff(w, 10), 10) \* should retain state


\* Note: SIE here; Open not available in this example
SIE(p, q) == <<p.type, q.type>> \in {
  \* Accept
  << "Deposit", "Deposit" >>,
  << "Withdraw", "Deposit" >>,
  \* Reject
  << "Deposit", "Open" >>,
  << "Withdraw", "Open" >>,
  << "Open", "Withdraw" >>
}

SCBC(p,q) ==  <<p.type, q.type>> \in {
\* %   |project://rebel-sco/examples/simple/Account.ebl|
\* % SCO^Accept size:4, SCO^Reject size:4, Delays: 8
\* %            Open   Deposit    Withdraw  Interest   
\* % Open         D       D          AR         D      
\* % Deposit      D      AR           D         D      
\* % Withdraw    AR       D           D         D      
\* % Interest     D       D           D        AR    
  << "Open", "Withdraw" >>,
  << "Deposit", "Deposit" >>,
  << "Withdraw", "Open" >>,
  << "Interest", "Interest" >>
}

\* Static CBC Definitions
\* independent of state. Operations p and q should be CBC for all possible states
StaticCBC(p, q) == SCBC(p,q)

\* pre[o \in AccountOperations, b \in Balance] == evalPre(o,b)
\* eff[o \in AccountOperations, b \in Balance] == evalEff(o,b)

\* ASSUME PrintT(pre)

\* \* INLINE tryout
\* \* alt approach with set of states where preconditions holds
\* BALANCE == 0..50
\* \* BALANCE == Nat
\* preStates(amount) == { b \in BALANCE : b - amount >=  0 }
\* ASSUME PrintT(preStates(40))
\* \* now preconditions check becomes s \in  preStates(50) or something.
\* postStates(amount) == {<<b, b_post>> \in BALANCE \X BALANCE : b + amount = b_post }
\* ASSUME PrintT(postStates(40))
\* ps40  == postStates(40)
\* ASSUME PrintT(50 \in {b_post \in Balance : <<b, b_post>> \in ps40 /\ b = 10})
\* \* INLINE tryout  end

\* \* Serializable actions with commutative events. Does CI detect this correctly?
\* \* Example from Weikum: Multi-level transactions
\* \* T1: a.-50, c.+50
\* \* T2: b.-40, c.+40 (different amounts to see distinction in values)
\* \* Accounts A and B live on same bank branch office and T1 and T2 increment branch total T
\* \* Added reads for T make sure CI detects this as non-serializable.

\* s0 == [k \in {A,B,C} |-> 100] @@ (T :> 0)

\* \* rt1 == << r(A, 100), w(A, 50), r(T,  0), w(T, 50), r(C, 140), w(C,190) >> 
\* \* rt2 == << r(B, 100), w(B, 60), r(T, 50), w(T, 90), r(C, 100), w(C,140) >> 

\* \* Operations on L1
\* \* InvariantWithdraw(balance, amount) == (balance - amount) >= 0
\* \* EffectWithdraw(balance,  amount) == balance - amount
\* \* EffectDeposit(balance,  amount) == balance + amount

\* \* PreWithdraw(amount) == [balance \in Balance |-> (balance - amount) >= 0]
\* \* EffWithdraw(amount) == [balance \in Balance |-> balance - amount]

\* \* PreDeposit(amount) == [balance \in Balance |-> TRUE]
\* \* EffDeposit(amount) == [balance \in Balance |-> balance + amount]

\* \* CDeposit[balance \in Balance] == PreDeposit(balance)

\* \* Transactions are Seq's of Operation:
\* \* Operations == [type: String, fields...]
\* \* [op: Operations,  key: Keys]
\* op(resource, event) == [ op |-> event , key |-> resource ]
\* t1 == << 
\*         \* Withdraw(A, 50)
\*         op(A, Withdraw(50))
\*         \* Deposit(C, 50)
\*        ,op(C, Deposit(50))
\*         \* TODO Withdraw also adds amount to T
\*         >>
\* t2 == << 
\*         \* Withdraw(A, 40)
\*         op(B, Withdraw(40))
\*         \* Deposit(C, 40)
\*        ,op(C, Deposit(40))
\*         \* TODO Withdraw also adds amount to T
\*         >>

\* bLabels == (t1 :> "t1") @@ (t2 :> "t2")
\* btransactions == DOMAIN bLabels

\* \* TransactionsTypeOK == TypeOKT(btransactions)

\* \* \* First check if we can build an execution:
\* s1 == (A :> 50) @@ (B :> 100) @@ (C :> 150) @@ (T :> 50)
\* Prop == test(Eff(s0, t1), s1)
\* s2 == (A :> 50) @@ (B :> 60) @@ (C :> 190) @@ (T :> 90)
\* Prop2 == test(Eff(s1, t2), s2)

\* \* \* ASSUME PrintT(PermSeqs({"t1", "t2"}))
\* \* ASSUME PrintT(btransactions)
\* \* \* ASSUME PrintT(SUBSET btransactions)
\* \* \* ASSUME PrintT(PermSeqs(btransactions)) \*  ERROR
\* \* \* ASSUME PrintT(executions(s0, {rt1}))
\* \* \* ASSUME PrintT(executions(s0, {rt2}))
\* \* \* ASSUME PrintT(executions(s0, btransactions))

\* \* To make it run TLC
\* Init == FALSE /\ Accounts' = Accounts
\* Next == FALSE /\ Accounts' = Accounts

=============================================================================
