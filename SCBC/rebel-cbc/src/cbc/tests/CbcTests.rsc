module cbc::tests::CbcTests

import cbc::Analysis;
import psac::IngSpecsRunner;
import List;
import IO;
import util::Math;
import String;

public loc simple = |project://rebel-cbc/examples/ser_alternative/simple/Account.ebl|;
public loc ser = |project://rebel-cbc/examples/ser_alternative/ser/Account.ebl|;

public loc verySimple = |project://rebel-cbc/examples/simple/Account.ebl|;

public str scoAssert = 
         "(declare-const e1 Event)
         '(declare-const e2 Event)

         '(declare-const state_before State)
         '(declare-const some_state State)
         '(assert (pre e2 some_state))
         
         '(declare-const state_post_e1 State)
  			 '(declare-const state_post_e2 State)
  			 '(declare-const state_post_e1_e2 State)
  			 '(declare-const state_post_e2_e1 State)
  			 '; bind post consts
  			 '(assert (post e1 state_before state_post_e1)) ; s e1
  			 '(assert (post e2 state_before state_post_e2)) ; s e2
  			 '(assert (post e2 state_post_e1 state_post_e1_e2)) ; s e1 e2
  			 '(assert (post e1 state_post_e2 state_post_e2_e1)) ; s e2 e1
  			 '(assert (not (=\> (and (pre e1 state_before))
         '        (and (= (pre e2 state_before) (pre e2 state_post_e1))
         '             (= state_post_e1_e2 state_post_e2_e1 )
         '        )
         ')))";
         
void printScoResults(SieResult resultAccept, SieResult resultReject) {
  println("SCO^Accept size:<size(resultAccept.compatible)>, SCO^Reject size:<size(resultReject.compatible)>, Delays: <size(resultAccept.allEvents * resultAccept.allEvents) - size(resultAccept.compatible) - size(resultReject.compatible)>");
  
  int maxEventNameLength = max([size(e) | e <- resultAccept.allEvents]) + 1;
  
  println(center("", maxEventNameLength) + intercalate(" ",[ center(e,maxEventNameLength) | e <- resultAccept.allEvents]));
  println(
  intercalate("\n",
    [ "<left(e1,maxEventNameLength)><
      intercalate(" ", [ "<center(getSieLetter(resultAccept.compatible, resultReject.compatible, e1, e2),maxEventNameLength)>"
      | str e2 <- resultAccept.allEvents
      ])
    >"
    | str e1 <- resultAccept.allEvents
    ]
    )
  );
}
  
void analyse(loc l) { return analyse(l, scoAcceptAssert, scoRejectAssert); }   
     
void analyse(loc l, str acceptAssert, str rejectAssert) { 
  SieResult resultAccept = runAssertAndIterateModels(l, smtAssert = acceptAssert);
    
  SieResult resultReject =  runAssertAndIterateModels(l, smtAssert = rejectAssert);
  
  println(l);
  printScoResults(resultAccept, resultReject);
}

void singleAnalyse(loc l, str smtAssert) { 
   SieResult result= runAssertAndIterateModels(l, smtAssert = smtAssert);
    
    println(l);
  printScoResults(result, result);
}

public str scoAcceptAssert = 
         "(declare-const e1 Event)
         '(declare-const e2 Event)

         '(declare-const state_before State)
         '(declare-const some_state State)
         '(assert (pre e2 some_state))
         
         '(declare-const state_post_e1 State)
         '(declare-const state_post_e2 State)
         '(declare-const state_post_e1_e2 State)
         '(declare-const state_post_e2_e1 State)
         '; bind post consts
         '(assert (post e1 state_before state_post_e1)) ; s e1
         '(assert (post e2 state_before state_post_e2)) ; s e2
         '(assert (post e2 state_post_e1 state_post_e1_e2)) ; s e1 e2
         '(assert (post e1 state_post_e2 state_post_e2_e1)) ; s e2 e1
         '(assert (not (=\> (and (pre e1 state_before))
         '                  (and (and (pre e2 state_before) (pre e2 state_post_e1))
         '                       (= state_post_e1_e2 state_post_e2_e1)
         '                  )
         ')))";
           
public str scoRejectAssert = 
         "(declare-const e1 Event)
         '(declare-const e2 Event)

         '(declare-const state_before State)
         '(declare-const some_state State)
         '(assert (pre e2 some_state))
         
         '(declare-const state_post_e1 State)
         '(declare-const state_post_e2 State)
         '(declare-const state_post_e1_e2 State)
         '(declare-const state_post_e2_e1 State)
         '; bind post consts
         '(assert (post e1 state_before state_post_e1)) ; s e1
         '(assert (post e2 state_before state_post_e2)) ; s e2
         '(assert (post e2 state_post_e1 state_post_e1_e2)) ; s e1 e2
         '(assert (post e1 state_post_e2 state_post_e2_e1)) ; s e2 e1
         '(assert (not (=\> (pre e1 state_before)
         '                  (and (not (pre e2 state_before)) (not (pre e2 state_post_e1))
         '                  ; nothing on state needed, because no change in state on reject
         '                  )
         ')))";         
         
         
public str scoWithStateAssert = 
  "; events
  '(declare-const e1 Event)
  '(declare-const e2 Event)
  '; events are valid in some state (no nonsense events, such as Deposit(-100))
  '(declare-const some_state1 State)
  '(assert (pre e1 some_state1))
  '(declare-const some_state2 State)
  '(assert (pre e2 some_state2))
  '; states, index shows applied events; s0 is inital state
  '(declare-const s0 State)         
  '(declare-const s01 State)
  '(declare-const s02 State)
  '(declare-const s012 State)
  '(declare-const s021 State)
  '; bind states using event
  '(define-fun apply ( (event Event) (pre_state State) (post_state State)) Bool
  '  (ite (pre  event pre_state)
  '    (post  event pre_state post_state) 
  '    (= post_state pre_state)
  '  ))
  '(assert (apply e1 s0 s01)) ; s e1
  '(assert (apply e2 s0 s02)) ; s e2
  '(assert (apply e2 s01 s012)) ; s e1 e2
  '(assert (apply e1 s02 s021)) ; s e2 e1
  '; eff function using defined events and states
  '(declare-fun eff ( Event State ) State)
  '(assert (= (eff e1 s0) s01))
  '(assert (= (eff e1 s02) s021))
  '(assert (= (eff e2 s0) s02))
  '(assert (= (eff e2 s01) s012))
  '; RetVal type to group return values
  '(declare-datatypes () (  ( RetVal (RetVal (success Bool) (state State)) ) ))
  '(define-fun retVal ( (event Event) (state State) ) RetVal
  '  (RetVal (pre event state) (eff event state) )
  ')
  '
  '(assert (not (and (= (retVal e1 s0) (retVal e1 s02))
  '                  (= (retVal e2 s01) (retVal e2 s0))
  ')))"; 
  
public str scoWithoutStateAssert = 
  "; events
  '(declare-const e1 Event)
  '(declare-const e2 Event)
  '; events are valid in some state (no nonsense events, such as Deposit(-100))
  '(declare-const some_state1 State)
  '(assert (pre e1 some_state1))
  '(declare-const some_state2 State)
  '(assert (pre e2 some_state2))
  '; states, index shows applied events; s0 is inital state
  '(declare-const s0 State)         
  '(declare-const s01 State)
  '(declare-const s02 State)
  '(declare-const s012 State)
  '(declare-const s021 State)
  '; bind states using event
  '(define-fun apply ( (event Event) (pre_state State) (post_state State)) Bool
  '  (ite (pre  event pre_state)
  '    (post  event pre_state post_state) 
  '    (= post_state pre_state)
  '  ))
  '(assert (apply e1 s0 s01)) ; s e1
  '(assert (apply e2 s0 s02)) ; s e2
  '(assert (apply e2 s01 s012)) ; s e1 e2
  '(assert (apply e1 s02 s021)) ; s e2 e1
  '; eff function using defined events and states
  '(declare-fun eff ( Event State ) State)
  '(assert (= (eff e1 s0) s01))
  '(assert (= (eff e1 s02) s021))
  '(assert (= (eff e2 s0) s02))
  '(assert (= (eff e2 s01) s012))
  '; RetVal type to group return values
  '(declare-datatypes () (  ( RetVal (RetVal (success Bool)) ) ))
  '(define-fun retVal ( (event Event) (state State) ) RetVal
  '  (RetVal (pre event state) )
  ')
  '
  '; property assert
  '(assert (not (and (= (retVal e1 s0)  (retVal e1 s02))
  '                  (= (retVal e2 s01) (retVal e2 s0))
  ')))";
  
public str scoRetvalAndPostStateAssert = 
  "; events
  '(declare-const e1 Event)
  '(declare-const e2 Event)
  '; events are valid in some state (no nonsense events, such as Deposit(-100))
  '(declare-const some_state1 State)
  '(assert (pre e1 some_state1))
  '(declare-const some_state2 State)
  '(assert (pre e2 some_state2))
  '; states, index shows applied events; s0 is inital state
  '(declare-const s0 State)         
  '(declare-const s01 State)
  '(declare-const s02 State)
  '(declare-const s012 State)
  '(declare-const s021 State)
  '; bind states using event
  '(define-fun apply ( (event Event) (pre_state State) (post_state State)) Bool
  '  (ite (pre  event pre_state) ; only change state is preconditions hold
  '    (post  event pre_state post_state) 
  '    (= post_state pre_state)
  '  ))
  '(assert (apply e1 s0 s01)) ; s e1
  '(assert (apply e2 s0 s02)) ; s e2
  '(assert (apply e2 s01 s012)) ; s e1 e2
  '(assert (apply e1 s02 s021)) ; s e2 e1
  '; eff function using defined events and states
  '(declare-fun eff ( Event State ) State)
  '(assert (= (eff e1 s0) s01))
  '(assert (= (eff e1 s02) s021))
  '(assert (= (eff e2 s0) s02))
  '(assert (= (eff e2 s01) s012))
  '; RetVal type to group return values
  '(declare-datatypes () (  ( RetVal (RetVal (success Bool)) ) ))
  '(define-fun retVal ( (event Event) (state State) ) RetVal
  '  (RetVal (pre event state) )
  ')
  '
  '; property assert
  '(assert (not (and (= (retVal e1 s0)  (retVal e1 s02))
  '                  (= (retVal e2 s01) (retVal e2 s0))
  '                  (= s012 s021)
  ')))";