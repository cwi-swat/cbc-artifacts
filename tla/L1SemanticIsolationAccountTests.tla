--------------------------- MODULE L1SemanticIsolationAccountTests ---------------------------
EXTENDS Sequences, FiniteSets, TLC, Integers, Util, L1ClientCentricIsolation

\* d == Deposit(40)
\* w == Withdraw(40)

\* Serializable actions with commutative events. Does CI detect this correctly?
\* Example from Weikum: Multi-level transactions
\* T1: a.-50, c.+50
\* T2: b.-40, c.+40 (different amounts to see distinction in values)
\* Accounts A and B live on same bank branch office and T1 and T2 increment branch total T
\* Added reads for T make sure CI detects this as non-serializable.

s0 == [k \in {A,B,C} |-> 100] @@ (T :> 0)

\* Transactions are Seq's of Operation:
\* Operations == [type: String, fields...]
\* [op: Operations,  key: Keys]
t1 == << 
        \* Withdraw(A, 50)
        op(A, Withdraw(50), OK)
        \* Deposit(C, 50)
       ,op(C, Deposit(50), OK)
        \* TODO Withdraw also adds amount to T
       ,op(T, Deposit(50), OK)
        >>
t2 == << 
        \* Withdraw(A, 40)
        op(B, Withdraw(40), OK)
        \* Deposit(C, 40)
       ,op(C, Deposit(40), OK)
        \* TODO Withdraw also adds amount to T
       ,op(T, Deposit(40), OK)
        >>
q == <<
       op(A, Query, 50)
      ,op(B, Query, 60)
      ,op(C, Query, 190)
      ,op(T, Query, 90)
      >>

bLabels == (t1 :> "t1") @@ (t2 :> "t2") @@ (q :> "q")
btransactions == DOMAIN bLabels

\* TransactionsTypeOK == TypeOKT(btransactions)

ASSUME PrintT("L1 SER Example")
\* \* First check if we can build an execution:
s1 == (A :> 50) @@ (B :> 100) @@ (C :> 150) @@ (T :> 50)
ASSUME test(effects(s0, t1), s1)
s2 == (A :> 50) @@ (B :> 60) @@ (C :> 190) @@ (T :> 90)
ASSUME test(effects(s1, t2), s2)

\* ASSUME PrintT(ppExecutions(executions(s0, btransactions), bLabels))

ASSUME SerializabilityDebug(s0, btransactions, bLabels)

\* NON SER example on L1
\* t1: A -50-> B
\* t2: +300%
nt1 == << 
        op(A, Withdraw(50), OK)
       ,op(B, Deposit(50), OK)
        >>
nt2 == << 
        op(A, Interest(3), OK)
       ,op(B, Interest(3), OK)
        >>
\* query  to "validate" end values, hacked using withdraw to check preconditions
\* PSAC allows these observed transactions
nq == <<
    \*    A |-> (100 - 50) * 3
       op(A, Query, 150)
    \*    B |-> (100  * 3) + 50
      ,op(B, Query, 250)
      >>

serq == <<
    \*    A |-> (100 - 50) * 3
       op(A, Query, 150)
    \*    B |-> (100 + 50) * 50
      ,op(B, Query, 450)
      >>

ns0 == [k \in {A,B} |-> 100]

nLabels == (nt1 :> "t1") @@ (nt2 :> "t2") @@ (nq :> "q")
ntransactions == DOMAIN nLabels

ASSUME PrintT("NON SER Example")
\* ASSUME PrintT(ppExecutions(executions(ns0, ntransactions), nLabels))

ASSUME SerializabilityDebug(ns0, ntransactions, nLabels) = FALSE



\* Counter example from 2PC
ASSUME PrintT("NON SER 2PC Example")
ccLabels == (
  <<
    [key |-> A, op |-> [amount |-> 0, type |-> "Deposit", id |-> "t1"], retVal |-> OK],
    [key |-> B, op |-> [amount |-> 1, type |-> "Deposit"], retVal |-> OK]>> :> "t1" @@ 
  <<
    [key |-> A, op |-> [amount |-> 0, type |-> "Deposit", id |-> "t2"], retVal |-> OK], 
    [key |-> B, op |-> [amount |-> 1, type |-> "Deposit"], retVal |-> OK]>> :> "t2" @@ 
  <<
    [key |-> B, op |-> [amount |-> 2, type |-> "Withdraw"], retVal |-> OK]>> :> "t3")

ccTransactions == DOMAIN ccLabels
ccInit == [k \in {A,B} |-> 0] 

ASSUME PrintT(ccTransactions)
ASSUME SerializabilityDebug(ccInit, ccTransactions, ccLabels)
\* TODO fix.. t1 and t2 contain same operations, in a set they are indistinquishable.
\* Bags? Or seqs argh or unique identifier somewhere
\* workaround by adding id to operation

\* CBC paper examples

cs0 == (A :> 0) @@ (B :> 100)

ct1 == << 
        \* Withdraw(A, 50)
        op(A, Deposit(10), OK)
        \* Deposit(C, 50)
       ,op(B, Withdraw(10), OK)
        >>
ct2 == << 
        \* Withdraw(A, 50)
        op(A, Deposit(20), OK)
        \* Deposit(C, 50)
       ,op(B, Withdraw(20), OK)
        >>
ct3 == << 
        \* Withdraw(A, 50)
        op(A, Withdraw(30), OK)
        \* Deposit(C, 50)
       ,op(B, Deposit(30), OK)
        >>
\* cq == <<
\*        op(A, Query(50))
\*       ,op(B, Query(60))
\*       ,op(C, Query(190))
\*       ,op(T, Query(90))
\*       >>

cLabels == (ct1 :> "t1") @@ (ct2 :> "t2") @@ (ct3 :> "t3")
ctransactions == DOMAIN cLabels

ASSUME PrintT("CBC paper example 1")
ASSUME SerializabilityDebug(cs0, ctransactions, cLabels)

ASSUME PrintT("CBC paper example 2, B |-> 0")
c2s0 == (A :> 0) @@ (B :> 0)
ASSUME ~SerializabilityDebug(c2s0, ctransactions, cLabels)


\* \* Problematic 2PC examples:
\* \* (t1 :> <<[key |-> A, op |-> [amount |-> 0, id |-> t1, retVal |-> FALSE, type |-> "Deposit"]]>> @@ t2 :> <<>> @@ t3 :> <<>>)

2pcLabels == (
  <<[key |-> A, op |-> [amount |-> 1, id |-> "t1", type |-> "Withdraw"], retVal |-> FALSE], [key |-> B, op |-> [amount |-> 1, id |-> "t1", type |-> "Deposit"], retVal |-> TRUE]>> :> "t1" @@ 
  <<[key |-> A, op |-> [amount |-> 1, id |-> "t2", type |-> "Deposit"], retVal |-> TRUE], [key |-> B, op |-> [amount |-> 1, id |-> "t2", type |-> "Withdraw"], retVal |-> FALSE]>> :> "t2" 
  \* @@ 
  \* <<>> :> "t3"
)

2pcTransactions == DOMAIN 2pcLabels
\* ccInit == [k \in {A,B} |-> 0] 

\* \* t1 :> <<[key |-> A, op |-> [amount |-> 0, id |-> t1, retVal |-> FALSE, type |-> "Deposit"]]>>

\* Results in NonSerializable because aborted transactions are also used to create next state.
\* Either add info on abortion, or remove aborted from set of transactions
\* 2PL/2PC no longer emits aborted operations/transactions
ASSUME ~SerializabilityDebug(ccInit, 2pcTransactions, 2pcLabels)

\* 2PL/PC Seed Bug trace, should be not SER

\* RW transactions
\* (t1 :> <<>> @@
\*  t2 :> <<[key |-> r2, op |-> "read", value |-> 0], [key |-> r2, op |-> "write", value |-> 1], 
\* [key |-> r1, op |-> "read", value |-> 1], [key |-> r1, op |-> "write", value |-> 2]>> @@
\*  t3 :> <<[key |-> r1, op |-> "read", value |-> 0], [key |-> r1, op |-> "write", value |-> 1], [key |-> r2, op |-> "read", value |-> 1], [key |-> r2, op |-> "write", value |-> 2]>>)

\* Corresponding L1 transactions
bugLabels == (
  <<>> :> "t1" @@ 
  << op(B, Deposit(1), OK),
  op(A, Deposit(1), OK) >> :> "t2" @@ 
  << op(A, Deposit(1), OK),
  op(B, Deposit(1), OK) >> :> "t3"
)

bugTransactions == DOMAIN bugLabels

\* Totally valid on L1 level...
\* Ander voorbeeld zoeken...
ASSUME SerializabilityDebug(ccInit, bugTransactions, bugLabels)

\* L1 counter example?
counterLabels == (
  <<>> :> "t1" @@ 
  << op(B, Deposit(1), OK),
  op(A, Withdraw(1), OK) >> :> "t2" @@ 
  << op(A, Withdraw(1), OK),
  op(B, Deposit(1), OK) >> :> "t3"
)

counterTransactions == DOMAIN counterLabels

\* klopt, waarom niet gevonden?
ASSUME ~SerializabilityDebug(ccInit, counterTransactions, counterLabels)

\* met interest
counter2Labels == (
  <<>> :> "t2" @@ \* iets met OK return values, not shown want aborted
  << op(B, Deposit(1), OK),
  op(A, Deposit(1), OK) >> :> "t3" @@ 
  << op(A, Interest(2), OK),
  op(B, Interest(2), OK) >> :> "t1" @@
  << op(A, Query, 1), \* t1, t3
  op(B, Query, 2) \* t3, t1
  >> :> "q"
)
counter2Transactions == DOMAIN counter2Labels
ASSUME ~SerializabilityDebug(ccInit, counter2Transactions, counter2Labels)
\* ASSUME Serializability(ccInit, counter2Transactions)
\*  waarom niet gevonden? Kan voorkomen door non-ser 2PL bug
\* omdat de q nodig is?

SerTest(labels) == SerializabilityDebug(ccInit, DOMAIN labels, labels)
\* Counter example met Q
\* (t1 :> <<>> @@ t2 :> <<[key |-> B, op |-> [id |-> t2, type |-> "Query"], retVal |-> 0], [key |-> A, op |-> [amount |-> 1, id |-> t2, type |-> "Deposit"], retVal |-> TRUE]>> @@ t3 :> <<[key |-> A, op |-> [id |-> t3, type |-> "Query"], retVal |-> 0], [key |-> B, op |-> [amount |-> 1, id |-> t3, type |-> "Deposit"], retVal |-> TRUE]>>)
counterQLabels == (
  \* <<>> :> "t1" @@ 
  <<op(B, Query, 0), op(A, Deposit(1), OK)>> :> "t2" @@ 
  <<op(A, Query, 0), op(B, Deposit(1), OK)>> :> "t3"
)
ASSUME ~SerTest(counterQLabels)
\* SCORE!

\* CBC unit tests
ASSUME CBC(0, Deposit(1), Deposit(2))
ASSUME ConstructiveCBC(0, <<Deposit(1)>>, Deposit(2))
ASSUME ConstructiveCBC(0, <<>>, Deposit(2))
ASSUME ConstructiveCBC(0, <<>>, Withdraw(1))
ASSUME ConstructiveCBC(0, <<>>, Query)

ASSUME ~ConstructiveCBC(0, <<Deposit(1)>>, Withdraw(1))
ASSUME ConstructiveCBC(1, <<Deposit(1)>>, Withdraw(1))
ASSUME \forall o \in AccountOperations: ConstructiveCBC(0, <<>>, o)

\* LoCA CBC checks
ASSUME ConstructiveCBC(0, <<>>, Withdraw(1))
ASSUME ~DynamicCBC(0, Withdraw(1), Deposit(1)) \* want -1 in 0 heeft andere retVal dan -1 in 0+1
ASSUME ~ConstructiveCBC(0, <<Withdraw(1)>>, Deposit(1))
\* ASSUME ConstructiveCBC(0, <<Withdraw(1)>>, Deposit(1))
ASSUME ConstructiveCBC(0, <<Withdraw(1), Deposit(1)>>, Deposit(1))

\* To make it run TLC
Init == FALSE /\ Accounts' = Accounts
Next == FALSE /\ Accounts' = Accounts

=============================================================================
