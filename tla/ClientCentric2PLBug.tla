-------------------------- MODULE ClientCentric2PLBug --------------------------
EXTENDS Naturals, TLC, Sequences, FiniteSets, Util
CONSTANTS transactions, resources

(*
2PL/2PC where processes interleave

Assumes that no messages are lost, but can be received out of order.

2PC for atomicity.
2PL for isolation => serializability
No deadlock, because TM is allowed to abort
*)

\* Client Centric instance for checking consistency levels
CC == INSTANCE L1ClientCentricIsolation WITH CbcConfig <- "dynamic"

op(r,e,rv) == CC!op(r,e,rv)

(* --algorithm 2pl
variables
\*  append send in the system
  msgs = {},
  \* lastMsg = {},
\*  reads and writes per transaction id
  operations = [ tId \in transactions |-> <<>> ]
  ;

define
  InitialState == [k \in resources |-> CC!InitialData]
end define;
  
macro sendMessage(msg) begin
  msgs := msgs \union {msg};
  \* lastMsg := msg;
end macro

fair process tm \in transactions
begin
  INIT: sendMessage([id |-> self, type |-> "VoteRequest"]);
  WAIT: either \* receive commit votes
    await \A rm \in resources: [id |-> self, type |-> "VoteCommit", rm |-> rm] \in msgs;
    sendMessage( [id |-> self, type |-> "GlobalCommit"]);
    goto COMMIT;
  or \* receive at least 1 abort votes
    await \E rm \in resources: [id |-> self, type |-> "VoteAbort", rm |-> rm] \in msgs;
    sendMessage([id |-> self, type |-> "GlobalAbort"]);
    goto ABORT;
  or \* or timeout, solves deadlock when two transactions lock each others resources
    sendMessage([id |-> self, type |-> "GlobalAbort"]);
    goto ABORT;
  end either;
  ABORT: goto Done;
  COMMIT: goto Done;
end process

fair process tr \in resources
  variables maxTxs = 5,
            voted = {}, committed = {}, aborted = {},
            state = InitialState[self]
begin TR_INIT:
while maxTxs >= 0 do
  either skip; \* skip to not deadlock
  or \* Wait on VoteRequest
    with tId \in transactions \ voted do 
      \* pick operation
      await [id |-> tId, type |-> "VoteRequest"] \in msgs;
      either \* If preconditions hold, VoteCommit, else VoteAbort
        sendMessage([id |-> tId, type |-> "VoteCommit", rm |-> self]);
        voted := voted \union {tId};
      or 
        sendMessage([id |-> tId, type |-> "VoteAbort", rm |-> self]);
        voted := voted \union {tId};
        aborted := aborted \union {tId};
        goto STEP;
      end either;
    end with;
  READY: \* Wait on Commit/Abort  
    either \* receive GlobalCommit
      with tId \in transactions \ committed do 
        await [id |-> tId, type |-> "GlobalCommit"] \in msgs;
        committed := committed \union {tId};
        \* Only committed operations are relevant.
        \* is state the correct state here, RetVal should be determined at original state when voting?
        with oper \in 
          \* Add id to make sure operation structures are unique.
          \* only with non-failing pre, because that was checked at Vote (with state there)
          { o @@ ("id" :> tId) 
          : o \in { o \in CC!Operations: CC!Pre(o, state) } } do
          \*      Add operations of local values to the relevant transaction's operations
            operations[tId] := operations[tId] \o << op(self, oper, CC!RetVal(oper, state)) >>;
            state := CC!Eff(oper, state);
        end with;
      end with;
    or \* receive GlobalAbort
      with tId \in transactions \ aborted do 
        await [id |-> tId, type |-> "GlobalAbort"] \in msgs;
        aborted := aborted \union {tId};
      end with;
    end either;
  end either;
  STEP: maxTxs := maxTxs - 1;
end while;
end process;

end algorithm *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-dc0d329e15a8bd54f865a0f0fe8a9b78
VARIABLES msgs, operations, pc

(* define statement *)
InitialState == [k \in resources |-> CC!InitialData]

VARIABLES maxTxs, voted, committed, aborted, state

vars == << msgs, operations, pc, maxTxs, voted, committed, aborted, state >>

ProcSet == (transactions) \cup (resources)

Init == (* Global variables *)
        /\ msgs = {}
        /\ operations = [ tId \in transactions |-> <<>> ]
        (* Process tr *)
        /\ maxTxs = [self \in resources |-> 5]
        /\ voted = [self \in resources |-> {}]
        /\ committed = [self \in resources |-> {}]
        /\ aborted = [self \in resources |-> {}]
        /\ state = [self \in resources |-> InitialState[self]]
        /\ pc = [self \in ProcSet |-> CASE self \in transactions -> "INIT"
                                        [] self \in resources -> "TR_INIT"]

INIT(self) == /\ pc[self] = "INIT"
              /\ msgs' = (msgs \union {([id |-> self, type |-> "VoteRequest"])})
              /\ pc' = [pc EXCEPT ![self] = "WAIT"]
              /\ UNCHANGED << operations, maxTxs, voted, committed, aborted, 
                              state >>

WAIT(self) == /\ pc[self] = "WAIT"
              /\ \/ /\ \A rm \in resources: [id |-> self, type |-> "VoteCommit", rm |-> rm] \in msgs
                    /\ msgs' = (msgs \union {([id |-> self, type |-> "GlobalCommit"])})
                    /\ pc' = [pc EXCEPT ![self] = "COMMIT"]
                 \/ /\ \E rm \in resources: [id |-> self, type |-> "VoteAbort", rm |-> rm] \in msgs
                    /\ msgs' = (msgs \union {([id |-> self, type |-> "GlobalAbort"])})
                    /\ pc' = [pc EXCEPT ![self] = "ABORT"]
                 \/ /\ msgs' = (msgs \union {([id |-> self, type |-> "GlobalAbort"])})
                    /\ pc' = [pc EXCEPT ![self] = "ABORT"]
              /\ UNCHANGED << operations, maxTxs, voted, committed, aborted, 
                              state >>

ABORT(self) == /\ pc[self] = "ABORT"
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << msgs, operations, maxTxs, voted, committed, 
                               aborted, state >>

COMMIT(self) == /\ pc[self] = "COMMIT"
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << msgs, operations, maxTxs, voted, committed, 
                                aborted, state >>

tm(self) == INIT(self) \/ WAIT(self) \/ ABORT(self) \/ COMMIT(self)

TR_INIT(self) == /\ pc[self] = "TR_INIT"
                 /\ IF maxTxs[self] >= 0
                       THEN /\ \/ /\ TRUE
                                  /\ pc' = [pc EXCEPT ![self] = "STEP"]
                                  /\ UNCHANGED <<msgs, voted, aborted>>
                               \/ /\ \E tId \in transactions \ voted[self]:
                                       /\ [id |-> tId, type |-> "VoteRequest"] \in msgs
                                       /\ \/ /\ msgs' = (msgs \union {([id |-> tId, type |-> "VoteCommit", rm |-> self])})
                                             /\ voted' = [voted EXCEPT ![self] = voted[self] \union {tId}]
                                             /\ pc' = [pc EXCEPT ![self] = "READY"]
                                             /\ UNCHANGED aborted
                                          \/ /\ msgs' = (msgs \union {([id |-> tId, type |-> "VoteAbort", rm |-> self])})
                                             /\ voted' = [voted EXCEPT ![self] = voted[self] \union {tId}]
                                             /\ aborted' = [aborted EXCEPT ![self] = aborted[self] \union {tId}]
                                             /\ pc' = [pc EXCEPT ![self] = "STEP"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                            /\ UNCHANGED << msgs, voted, aborted >>
                 /\ UNCHANGED << operations, maxTxs, committed, state >>

STEP(self) == /\ pc[self] = "STEP"
              /\ maxTxs' = [maxTxs EXCEPT ![self] = maxTxs[self] - 1]
              /\ pc' = [pc EXCEPT ![self] = "TR_INIT"]
              /\ UNCHANGED << msgs, operations, voted, committed, aborted, 
                              state >>

READY(self) == /\ pc[self] = "READY"
               /\ \/ /\ \E tId \in transactions \ committed[self]:
                          /\ [id |-> tId, type |-> "GlobalCommit"] \in msgs
                          /\ committed' = [committed EXCEPT ![self] = committed[self] \union {tId}]
                          /\ \E oper \in { o @@ ("id" :> tId)
                                         : o \in { o \in CC!Operations: CC!Pre(o, state[self]) } }:
                               /\ operations' = [operations EXCEPT ![tId] = operations[tId] \o << op(self, oper, CC!RetVal(oper, state[self])) >>]
                               /\ state' = [state EXCEPT ![self] = CC!Eff(oper, state[self])]
                     /\ UNCHANGED aborted
                  \/ /\ \E tId \in transactions \ aborted[self]:
                          /\ [id |-> tId, type |-> "GlobalAbort"] \in msgs
                          /\ aborted' = [aborted EXCEPT ![self] = aborted[self] \union {tId}]
                     /\ UNCHANGED <<operations, committed, state>>
               /\ pc' = [pc EXCEPT ![self] = "STEP"]
               /\ UNCHANGED << msgs, maxTxs, voted >>

tr(self) == TR_INIT(self) \/ STEP(self) \/ READY(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in transactions: tm(self))
           \/ (\E self \in resources: tr(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in transactions : WF_vars(tm(self))
        /\ \A self \in resources : WF_vars(tr(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-82959b5d597904374cffb99ed62662b0


Message == [id: transactions, type: {"VoteRequest", "GlobalCommit", "GlobalAbort"}] \union
  [id: transactions, type: {"VoteAbort", "VoteCommit"}, rm: resources]

TypeOK == /\ msgs \subseteq Message
          /\ \A res \in resources: 
             /\ committed[res] \in SUBSET transactions
             /\ aborted[res] \in SUBSET transactions
             /\ voted[res] \in SUBSET transactions

Atomicity == 
\* When resource are done
  \A id \in transactions: pc[id]="Done" => 
    \A a1,a2 \in resources:
          \* no participants differ from result aborted or committed
        ~ /\ id \in aborted[a1] 
          /\ id \in committed[a2]
          
AllTransactionsFinish == <>(\A t \in transactions: pc[t] = "Done")

ccTransactions == Range(operations) \* todo only committed transactions, filter by committed[tid] or state of TM

CCTypeOK == CC!TypeOKT(ccTransactions)

Serializable == 
\*  PrintT(<<"InitialState", InitialState>>) /\
\*  PrintT(<<"ccTransactions", ccTransactions>>) /\
  CC!Serializability(InitialState, ccTransactions)
    
\* SnapshotIsolation == CC!SnapshotIsolation(InitialState, ccTransactions)
\* ReadCommitted == CC!ReadCommitted(InitialState, ccTransactions)
\* ReadUncommitted == CC!ReadUncommitted(InitialState, ccTransactions)

=============================================================================
\* Modification History
\* Last modified Wed Jun 24 13:52:10 CEST 2020 by tim
\* Created Tue Apr 28 16:41:42 CEST 2020 by tim
