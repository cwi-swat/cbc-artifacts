-------------------------- MODULE AbstractLoCA --------------------------
EXTENDS Naturals, TLC, Sequences, FiniteSets, Util
CONSTANTS transactions, resources

(*
2PL/2PC where processes interleave

Assumes that no messages are lost, but can be received out of order.

2PC for atomicity.
CBC (return value commutativity) for isolation => Return-value serializability
No deadlock, because TM is allowed to abort
*)

\* Client Centric instance for checking consistency levels
CC == INSTANCE L1ClientCentricIsolation WITH CbcConfig <- "dynamic"

op(r,e,rv) == CC!op(r,e,rv)

(* --algorithm abstractLoCA
variables
\*  append send in the system
  msgs = {},
  \* lastMsg = {},
\*  reads and writes per transaction id
  operations = [ tId \in transactions |-> <<>> ],
  tcommitted = {} \* all committed transaction ids
  ;

define
  InitialState == [k \in resources |-> CC!InitialData]
  \* AbstractOperation == [op: Operations, key: resources]
  \* AbstractTransaction == SUBSET AbstractOperation
  \* Transactions == SUBSET AbstractOperation 
  \* TODO somehow create set of all possible transactions with length n.
  \* use TR to take operations from it randomly for the correct key (to simulate out of order delivery), add to `operations` with current retVal
  \* Abstract away from abort, which would not show up in schedule anyway
  \* Then check them using RV-SER
  \* 
  \* Get the operations from inProgress, without tId
  ops(inProgress) == SeqMap(LAMBDA pair: pair.op, inProgress)
  \* ASSUME test(ops(<<[tId |-> "tId1", op |-> "op1"], [tId |-> "tId2", op |-> "op2"]>>), << "op1", "op2" >>) 
  \* Operations == CC!Operations \*  CC!DepositType \union CC!WithdrawType \union CC!InterestType \union {CC!Query}
  \* Operations == {CC!Deposit(1), CC!Withdraw(1), CC!Query}
  \* to detect violation when p_qp==p_pq is omitted from cbc. Needs Q to 
  Operations == {CC!Deposit(1), CC!Deposit(2), CC!Query}
  \* Operations == {CC!Deposit(1), CC!Query} \* Query should always be delay when deposit in progress
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
    tcommitted := tcommitted \union {self};
    goto Done; \* goto COMMIT
  or \* receive at least 1 abort votes
    await \E rm \in resources: [id |-> self, type |-> "VoteAbort", rm |-> rm] \in msgs;
    sendMessage([id |-> self, type |-> "GlobalAbort"]);
    goto Done; \* goto ABORT
  or \* or timeout, solves deadlock when two transactions lock each others resources
    sendMessage([id |-> self, type |-> "GlobalAbort"]);
    goto Done; \* goto ABORT
  end either;
end process

fair process tr \in resources
  variables 
            voted = {}, 
            rcommitted = {}, 
            aborted = {},
            queued = {},
            inProgress = <<>>, \* [tId |-> .., op |-> .., delayed |-> BOOLEAN]
            delayed = <<>>,
            state = InitialState[self]
begin
TR_INIT:
  \* receive and process until all transactions are either locally committed or aborted
while ~(\A t \in transactions: t \in rcommitted \/ t \in aborted) do
  with tId \in transactions do 
    either \* all receive messages
      await [id |-> tId, type |-> "VoteRequest"] \in msgs /\ tId \notin voted;
      either \* If CBC
        \* TODO: maybe more up, since abort is also CBC (or different CBC^Reject version for abort)
        with oper \in { o @@ ("tId" :> tId) 
                  : o \in { o \in Operations: CC!ConstructiveCBC(state, ops(inProgress), o) } } do
          inProgress := Append(inProgress, [tId |-> tId, op |-> oper]);
        end with;
        sendMessage([id |-> tId, type |-> "VoteCommit", rm |-> self]);
        voted := voted \union {tId};
      or \* also CBC, but not interested in specific operation
        sendMessage([id |-> tId, type |-> "VoteAbort", rm |-> self]);
        voted := voted \union {tId};
        aborted := aborted \union {tId};
      or \* delay, so not direct accept (by CBC) and also not direct reject/abort, so delay until dependent operations finish
        \* Alternatively model selection of oper after msg
        \* check for empty `inProgress` should not be needed because ~CBC is FALSE with empty inProgress, so oper can't be picked
        with oper \in 
          { o @@ ("tId" :> tId) 
                  : o \in { o \in Operations: ~CC!ConstructiveCBC(state, ops(inProgress), o) } } do
          delayed := Append(delayed, [tId |-> tId, op |-> oper]); 
          voted := voted \union {tId}; \* not really votes, but to not receive twice
        end with;
      end either;
      goto TR_INIT; \* loop back to start since no "applies" are possible after only vote
    or \* receive GlobalCommit
      await /\ [id |-> tId, type |-> "GlobalCommit"] \in msgs 
            /\ tId \in voted /\ tId \notin queued;
        queued := queued \union {tId};
        goto PROCESS_QUEUED;
    or \* receive GlobalAbort
      await /\ [id |-> tId, type |-> "GlobalAbort"] \in msgs 
            /\ tId \in voted /\ tId \notin aborted;
        aborted := aborted \union {tId};       
        inProgress := SelectSeq(inProgress, LAMBDA e: e.tId /= tId);  \* remove from `inProgress` or `delayed`
        delayed := SelectSeq(delayed, LAMBDA e: e.tId /= tId);
        goto PROCESS_QUEUED;
      \* end with;
    end either;
  end with;
  PROCESS_QUEUED:  \* Now handle queued (ready for commit/apply) items
  while /\ ~IsEmpty(inProgress) 
        /\ Head(inProgress).tId \in queued
    do
    with inP = Head(inProgress) do
      \* add to operations for RV-check
      operations[inP.tId] := operations[inP.tId] \o << op(self, inP.op, CC!RetVal(inP.op, state)) >>;
      state := CC!Eff(inP.op, state); \* Apply Eff to state
      inProgress := Tail(inProgress); \*Remove(inProgress, Cm);
      queued := queued \ {inP.tId}; \* no longer queued, but Eff applied
      rcommitted := rcommitted \union {inP.tId}; \* keep track of committed transactions
    \* end if;
    end with;
    PROCESS_DELAYED: 
    \*  if head of delayed is CBC, then it can commit or abort
      while ~IsEmpty(delayed) /\ CC!ConstructiveCBC(state, ops(inProgress), Head(delayed).op) do
        either 
          sendMessage([id |-> Head(delayed).tId, type |-> "VoteCommit", rm |-> self]);
        inProgress := Append(inProgress, Head(delayed));
        or 
          sendMessage([id |-> Head(delayed).tId, type |-> "VoteAbort", rm |-> self]);
          aborted := aborted \union {Head(delayed).tId};
        end either;
        delayed := Tail(delayed);
    end while;
  end while;
end while;
end process;

end algorithm *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-eed4c586c96395df96eae21cfae3c1d3
VARIABLES msgs, operations, tcommitted, pc

(* define statement *)
InitialState == [k \in resources |-> CC!InitialData]









ops(inProgress) == SeqMap(LAMBDA pair: pair.op, inProgress)




Operations == {CC!Deposit(1), CC!Deposit(2), CC!Query}

VARIABLES voted, rcommitted, aborted, queued, inProgress, delayed, state

vars == << msgs, operations, tcommitted, pc, voted, rcommitted, aborted, 
           queued, inProgress, delayed, state >>

ProcSet == (transactions) \cup (resources)

Init == (* Global variables *)
        /\ msgs = {}
        /\ operations = [ tId \in transactions |-> <<>> ]
        /\ tcommitted = {}
        (* Process tr *)
        /\ voted = [self \in resources |-> {}]
        /\ rcommitted = [self \in resources |-> {}]
        /\ aborted = [self \in resources |-> {}]
        /\ queued = [self \in resources |-> {}]
        /\ inProgress = [self \in resources |-> <<>>]
        /\ delayed = [self \in resources |-> <<>>]
        /\ state = [self \in resources |-> InitialState[self]]
        /\ pc = [self \in ProcSet |-> CASE self \in transactions -> "INIT"
                                        [] self \in resources -> "TR_INIT"]

INIT(self) == /\ pc[self] = "INIT"
              /\ msgs' = (msgs \union {([id |-> self, type |-> "VoteRequest"])})
              /\ pc' = [pc EXCEPT ![self] = "WAIT"]
              /\ UNCHANGED << operations, tcommitted, voted, rcommitted, 
                              aborted, queued, inProgress, delayed, state >>

WAIT(self) == /\ pc[self] = "WAIT"
              /\ \/ /\ \A rm \in resources: [id |-> self, type |-> "VoteCommit", rm |-> rm] \in msgs
                    /\ msgs' = (msgs \union {([id |-> self, type |-> "GlobalCommit"])})
                    /\ tcommitted' = (tcommitted \union {self})
                    /\ pc' = [pc EXCEPT ![self] = "Done"]
                 \/ /\ \E rm \in resources: [id |-> self, type |-> "VoteAbort", rm |-> rm] \in msgs
                    /\ msgs' = (msgs \union {([id |-> self, type |-> "GlobalAbort"])})
                    /\ pc' = [pc EXCEPT ![self] = "Done"]
                    /\ UNCHANGED tcommitted
                 \/ /\ msgs' = (msgs \union {([id |-> self, type |-> "GlobalAbort"])})
                    /\ pc' = [pc EXCEPT ![self] = "Done"]
                    /\ UNCHANGED tcommitted
              /\ UNCHANGED << operations, voted, rcommitted, aborted, queued, 
                              inProgress, delayed, state >>

tm(self) == INIT(self) \/ WAIT(self)

TR_INIT(self) == /\ pc[self] = "TR_INIT"
                 /\ IF ~(\A t \in transactions: t \in rcommitted[self] \/ t \in aborted[self])
                       THEN /\ \E tId \in transactions:
                                 \/ /\ [id |-> tId, type |-> "VoteRequest"] \in msgs /\ tId \notin voted[self]
                                    /\ \/ /\ \E oper \in     { o @@ ("tId" :> tId)
                                                         : o \in { o \in Operations: CC!ConstructiveCBC(state[self], ops(inProgress[self]), o) } }:
                                               inProgress' = [inProgress EXCEPT ![self] = Append(inProgress[self], [tId |-> tId, op |-> oper])]
                                          /\ msgs' = (msgs \union {([id |-> tId, type |-> "VoteCommit", rm |-> self])})
                                          /\ voted' = [voted EXCEPT ![self] = voted[self] \union {tId}]
                                          /\ UNCHANGED <<aborted, delayed>>
                                       \/ /\ msgs' = (msgs \union {([id |-> tId, type |-> "VoteAbort", rm |-> self])})
                                          /\ voted' = [voted EXCEPT ![self] = voted[self] \union {tId}]
                                          /\ aborted' = [aborted EXCEPT ![self] = aborted[self] \union {tId}]
                                          /\ UNCHANGED <<inProgress, delayed>>
                                       \/ /\ \E oper \in { o @@ ("tId" :> tId)
                                                                 : o \in { o \in Operations: ~CC!ConstructiveCBC(state[self], ops(inProgress[self]), o) } }:
                                               /\ delayed' = [delayed EXCEPT ![self] = Append(delayed[self], [tId |-> tId, op |-> oper])]
                                               /\ voted' = [voted EXCEPT ![self] = voted[self] \union {tId}]
                                          /\ UNCHANGED <<msgs, aborted, inProgress>>
                                    /\ pc' = [pc EXCEPT ![self] = "TR_INIT"]
                                    /\ UNCHANGED queued
                                 \/ /\ /\ [id |-> tId, type |-> "GlobalCommit"] \in msgs
                                       /\ tId \in voted[self] /\ tId \notin queued[self]
                                    /\ queued' = [queued EXCEPT ![self] = queued[self] \union {tId}]
                                    /\ pc' = [pc EXCEPT ![self] = "PROCESS_QUEUED"]
                                    /\ UNCHANGED <<msgs, voted, aborted, inProgress, delayed>>
                                 \/ /\ /\ [id |-> tId, type |-> "GlobalAbort"] \in msgs
                                       /\ tId \in voted[self] /\ tId \notin aborted[self]
                                    /\ aborted' = [aborted EXCEPT ![self] = aborted[self] \union {tId}]
                                    /\ inProgress' = [inProgress EXCEPT ![self] = SelectSeq(inProgress[self], LAMBDA e: e.tId /= tId)]
                                    /\ delayed' = [delayed EXCEPT ![self] = SelectSeq(delayed[self], LAMBDA e: e.tId /= tId)]
                                    /\ pc' = [pc EXCEPT ![self] = "PROCESS_QUEUED"]
                                    /\ UNCHANGED <<msgs, voted, queued>>
                       ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                            /\ UNCHANGED << msgs, voted, aborted, queued, 
                                            inProgress, delayed >>
                 /\ UNCHANGED << operations, tcommitted, rcommitted, state >>

PROCESS_QUEUED(self) == /\ pc[self] = "PROCESS_QUEUED"
                        /\ IF /\ ~IsEmpty(inProgress[self])
                              /\ Head(inProgress[self]).tId \in queued[self]
                              THEN /\ LET inP == Head(inProgress[self]) IN
                                        /\ operations' = [operations EXCEPT ![inP.tId] = operations[inP.tId] \o << op(self, inP.op, CC!RetVal(inP.op, state[self])) >>]
                                        /\ state' = [state EXCEPT ![self] = CC!Eff(inP.op, state[self])]
                                        /\ inProgress' = [inProgress EXCEPT ![self] = Tail(inProgress[self])]
                                        /\ queued' = [queued EXCEPT ![self] = queued[self] \ {inP.tId}]
                                        /\ rcommitted' = [rcommitted EXCEPT ![self] = rcommitted[self] \union {inP.tId}]
                                   /\ pc' = [pc EXCEPT ![self] = "PROCESS_DELAYED"]
                              ELSE /\ pc' = [pc EXCEPT ![self] = "TR_INIT"]
                                   /\ UNCHANGED << operations, rcommitted, 
                                                   queued, inProgress, state >>
                        /\ UNCHANGED << msgs, tcommitted, voted, aborted, 
                                        delayed >>

PROCESS_DELAYED(self) == /\ pc[self] = "PROCESS_DELAYED"
                         /\ IF ~IsEmpty(delayed[self]) /\ CC!ConstructiveCBC(state[self], ops(inProgress[self]), Head(delayed[self]).op)
                               THEN /\ \/ /\ msgs' = (msgs \union {([id |-> Head(delayed[self]).tId, type |-> "VoteCommit", rm |-> self])})
                                          /\ inProgress' = [inProgress EXCEPT ![self] = Append(inProgress[self], Head(delayed[self]))]
                                          /\ UNCHANGED aborted
                                       \/ /\ msgs' = (msgs \union {([id |-> Head(delayed[self]).tId, type |-> "VoteAbort", rm |-> self])})
                                          /\ aborted' = [aborted EXCEPT ![self] = aborted[self] \union {Head(delayed[self]).tId}]
                                          /\ UNCHANGED inProgress
                                    /\ delayed' = [delayed EXCEPT ![self] = Tail(delayed[self])]
                                    /\ pc' = [pc EXCEPT ![self] = "PROCESS_DELAYED"]
                               ELSE /\ pc' = [pc EXCEPT ![self] = "PROCESS_QUEUED"]
                                    /\ UNCHANGED << msgs, aborted, inProgress, 
                                                    delayed >>
                         /\ UNCHANGED << operations, tcommitted, voted, 
                                         rcommitted, queued, state >>

tr(self) == TR_INIT(self) \/ PROCESS_QUEUED(self) \/ PROCESS_DELAYED(self)

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

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-5d7b6f830049455b1ee1794672dcde9a


Message == [id: transactions, type: {"VoteRequest", "GlobalCommit", "GlobalAbort"}] \union
  [id: transactions, type: {"VoteAbort", "VoteCommit"}, rm: resources]

TypeOK == /\ msgs \subseteq Message
          /\ \A res \in resources: 
            \*  /\ committed[res] \in SUBSET transactions
             /\ aborted[res] \in SUBSET transactions
             /\ voted[res] \in SUBSET transactions

Atomicity == 
\* When resource are done
  \A id \in transactions: pc[id]="Done" => 
    \A a1,a2 \in resources:
          \* no participants differ from result aborted or committed
        ~ /\ id \in aborted[a1] 
          /\ id \in rcommitted[a2]
          
AllTransactionsFinish == <>(\A t \in transactions: pc[t] = "Done")
AllResourcesFinish == <>(\A r \in resources: pc[r] = "Done" /\ IsEmpty(inProgress[r]))
ResourcesFinishAllTransactions == \A r \in resources: pc[r] = "Done" => (IsEmpty(inProgress[r]) /\ IsEmpty(delayed[r]))

\* When all transactions finish, all resources should also eventually have empty inProgress (and stay that way)
AllTransactionsAreApplied == \A t \in transactions: pc[t] = "Done" => 
  <>[](\A r \in resources: IsEmpty(inProgress[r]))

ccTransactions == { operations[tId] : tId \in tcommitted }

CCTypeOK == CC!TypeOKT(ccTransactions)

Serializable == 
  CC!Serializability(InitialState, ccTransactions)
    
\* SnapshotIsolation == CC!SnapshotIsolation(InitialState, ccTransactions)
\* ReadCommitted == CC!ReadCommitted(InitialState, ccTransactions)
\* ReadUncommitted == CC!ReadUncommitted(InitialState, ccTransactions)

=============================================================================
\* Modification History
\* Last modified Wed Jun 24 13:52:10 CEST 2020 by tim
\* Created Tue Apr 28 16:41:42 CEST 2020 by tim
