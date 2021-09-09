---- MODULE ClientCentric2PL_MC ----
EXTENDS ClientCentric2PL, TLC

CONSTANTS
t1, t2, t3, t4
CONSTANTS
A, B, C

mc_transactions == {t1,t2}
mc_resources == {A,B}
mc_symm == Permutations(mc_transactions) \union Permutations(mc_resources)

tLabels == (t1 :> "t1") @@ (t2 :> "t2") @@ (t3 :> "t3")  @@ (t4 :> "t4")

SerializabilityDebug == CC!SerializabilityDebug(InitialState, ccTransactions, tLabels)

\* ASSUME PrintT(CC!Transaction)
\* ASSUME <<[key |-> A, op |-> [amount |-> 1, type |-> "Deposit"]]>>  \in CC!Transaction

=============================================================================
