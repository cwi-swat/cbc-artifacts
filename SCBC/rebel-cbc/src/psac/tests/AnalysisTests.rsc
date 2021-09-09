module psac::tests::AnalysisTests

import psac::Analysis;
import List;

test bool findCompatibleActions() = {
  //tuple[EventCompatibility incompatible, EventCompatibility compatible] result = runPsacAssertAndIterateModels(accountLoc, smtAssert = psacAssert);
  SieResult result = runPsacAssertAndIterateModels(accountLoc, smtAssert = psacAssert);
  
  // e2 is dependent on e1
  equal(result.incompatible, [
    <"Block","Block">,
    <"Block","Close">,
    <"Block","Deposit">,
    <"Block","Interest">,
    <"Block","Unblock">,
    <"Block","Withdraw">,
    <"Close","Block">,
    <"Close","Close">,
    <"Close","Deposit">,
    <"Close","Interest">,
    <"Deposit","Close">, 
    <"Deposit","Withdraw">,
    <"Interest","Close">,
    <"Interest","Withdraw">,
    <"OpenAccount","Block">,
    <"OpenAccount","Deposit">,
    <"OpenAccount","Interest">,
    <"OpenAccount","OpenAccount">,
    <"OpenAccount","Withdraw">,
    <"Unblock","Block">,
    <"Unblock","Close">,
    <"Unblock","Deposit">,
    <"Unblock","Interest">,
    <"Unblock","Unblock">,
    <"Unblock","Withdraw">,
    <"Withdraw","Close">,
    <"Withdraw","Withdraw">
  ]);
  // e2 is INdependent on e1, either direct reject or direct accept
  equal(result.compatible, [
    <"Block","OpenAccount">, //FailFast (FF)
    <"Close","OpenAccount">, //FF
    <"Close","Unblock">, //FF
    <"Close","Withdraw">, //FF
    <"Deposit","Block">, 
    <"Deposit","Deposit">,
    <"Deposit","Interest">,
    <"Deposit","OpenAccount">, //FF
    <"Deposit","Unblock">, //FF
    <"Interest","Block">, 
    <"Interest","Deposit">,  
    <"Interest","Interest">,
    <"Interest","OpenAccount">, //FF
    <"Interest","Unblock">, //FF
    <"OpenAccount","Close">, //FF
    <"OpenAccount","Unblock">, //F
    <"Unblock","OpenAccount">, //FF
    <"Withdraw","Block">,
    <"Withdraw","Deposit">,
    <"Withdraw","Interest">,
    <"Withdraw","OpenAccount">, //FF
    <"Withdraw","Unblock"> //FF
  ]);
};

test bool findDirectAcceptActions() = {
  SieResult result = runPsacAssertAndIterateModels(accountLoc, smtAssert = psacAssertAccept);
  
  // e2 can always be accepted when e1 in progress
  equal(result.compatible, [
    <"Deposit","Block">, 
    <"Deposit","Deposit">,
    <"Deposit","Interest">,
    <"Interest","Block">, 
    <"Interest","Deposit">,  
    <"Interest","Interest">,
    <"Withdraw","Block">,
    <"Withdraw","Deposit">,
    <"Withdraw","Interest">
  ]);
};

test bool findFailFastActions() = {
  SieResult result = runPsacAssertAndIterateModels(accountLoc, smtAssert = psacAssertDecline);
  
  // e2 is INdependent on e1, direct reject
  equal(result.compatible, [
    <"Block","OpenAccount">, //FailFast (FF)
    <"Close","OpenAccount">, //FF
    <"Close","Unblock">, //FF
    <"Close","Withdraw">, //FF
    <"Deposit","OpenAccount">, //FF
    <"Deposit","Unblock">, //FF
    <"Interest","OpenAccount">, //FF
    <"Interest","Unblock">, //FF
    <"OpenAccount","Close">, //FF
    <"OpenAccount","Unblock">, //F
    <"Unblock","OpenAccount">, //FF
    <"Withdraw","OpenAccount">, //FF
    <"Withdraw","Unblock"> //FF
  ]);
};

test bool compatibleActionsShouldBeFailFastActionsAndDirectAcceptedActions() = {
  SieResult result = runPsacAssertAndIterateModels(accountLoc, smtAssert = psacAssert);
  
  SieResult resultA = runPsacAssertAndIterateModels(accountLoc, smtAssert = psacAssertAccept);
  SieResult resultD = runPsacAssertAndIterateModels(accountLoc, smtAssert = psacAssertDecline);
  
  equal(result.compatible, sort((resultA.compatible + resultD.compatible)));
};

bool equal(list[&A] found, list[&A] expected) = {
  if(found == expected) {
    return true;
  } else {
    throw "Missing: <found - expected>. <found> is not equal to <expected>";
  };
};