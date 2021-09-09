---- MODULE ClientCentric2PLBug_MC ----
EXTENDS ClientCentric2PLBug, TLC

CONSTANTS
t1, t2, t3, t4
CONSTANTS
A, B, C

mc_transactions == {t1,t2,t3}
mc_resources == {A,B}
mc_symm == Permutations(mc_transactions) \union Permutations(mc_resources)

tLabels == (t1 :> "t1") @@ (t2 :> "t2") @@ (t3 :> "t3")  @@ (t4 :> "t4")

SerializabilityDebug == CC!SerializabilityDebug(InitialState, ccTransactions, tLabels)

=============================================================================
