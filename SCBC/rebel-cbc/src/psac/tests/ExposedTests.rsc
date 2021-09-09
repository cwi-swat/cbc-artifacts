module psac::tests::ExposedTests

import psac::Analysis;
import psac::IngSpecsRunner;
//import List;
import IO;

public loc accountWithName = |project://rebel-sco/examples/return_value/Account.ebl|;
public loc AccountChangeName = |project://rebel-sco/examples/return_value/AccountChangeName.ebl|;

public loc agreement = |project://rebel-sco/examples/return_value/nested_sync/Agreement.ebl|;
public loc nestedSyncAccount = |project://rebel-sco/examples/return_value/nested_sync/Account.ebl|;

void returnVals(loc l) { 
   tuple[EventCompatibility incompatible, EventCompatibility sieAccept, list[str] allEvents, SpecInfo info] resultAccept = 
    runPsacAssertAndIterateModels(l, smtAssert = psacAssertAccept);
    
  tuple[EventCompatibility incompatible, EventCompatibility sieReject, list[str] allEvents, SpecInfo info] resultReject = 
    runPsacAssertAndIterateModels(l, smtAssert = psacAssertDecline);
  
  println(l);
  printSieResults(resultAccept, resultReject);
}


// Exposed TPCC
loc exposedLoc = |file:///Users/tim/workspace/tim-phd/papers/2019Exposed/simple-account.exposed.smt|;

public str psacExposedAssertAccept = "(declare-const e1 Event)
         '(declare-const e2 Event)
         '(declare-const state_post_e1 State)
         '(declare-const state_before State)
         '(declare-const e2_exposed Exposed)
         '(declare-const some_state State)
         '(assert (pre e2 some_state))
         '(assert (exposed e2 state_before e2_exposed))
         '(assert (not (=\> (and (pre e1 state_before) (post e1 state_before state_post_e1))
         '             (and (pre e2 state_before) (pre e2 state_post_e1) (exposed e2 state_before e2_exposed) (exposed e2 state_post_e1 e2_exposed))
         ')))";
         
public str psacExposedAssertDecline = "(declare-const e1 Event)
         '(declare-const e2 Event)
         '(declare-const state_post_e1 State)
         '(declare-const state_before State)
         '(declare-const e2_exposed Exposed)
         '(declare-const some_state State)
         '(assert (pre e2 some_state))
         '(assert (exposed e2 state_before e2_exposed))
         '(assert (not (=\> (and (pre e1 state_before) (post e1 state_before))
         '             (and (not (pre e2 state_before)) (not (pre e2 state_post_e1)))
         ')))";

bool exposed() = bprintln("<sieAnalysis(exposedLoc, {"Deposit", "Withdraw"}, smtAssert = psacAssertAccept)>");

SieResult district() = sieAnalysis(|file:///Users/tim/workspace/tim-phd/papers/2019Exposed/District.smt2|,
   {"Payment_D_updateYTD", "StockLevel_D_read", "NewOrder_D_useTaxAndOrderId"}, smtAssert = psacExposedAssertAccept);
   
SieResult districtReject() = sieAnalysis(|file:///Users/tim/workspace/tim-phd/papers/2019Exposed/District.smt2|,
   {"Payment_D_updateYTD", "StockLevel_D_read", "NewOrder_D_useTaxAndOrderId"}, smtAssert = psacExposedAssertDecline);
   
void printResults() {
  printSieResults(district(), districtReject());
}

void printResultsOriginal() {
  res = getResults(districtLoc);
  printSieResults(res.resultAccept, res.resultReject);  
}

