module psac::tests::SerAlternativeTests

import psac::Analysis;
import psac::IngSpecsRunner;
//import List;
import IO;

public loc simple = |project://rebel-sco/examples/ser_alternative/simple/Account.ebl|;
public loc ser = |project://rebel-sco/examples/ser_alternative/ser/Account.ebl|;

void analyse(loc l) { 
   tuple[EventCompatibility incompatible, EventCompatibility sieAccept, list[str] allEvents, SpecInfo info] resultAccept = 
    runPsacAssertAndIterateModels(l, smtAssert = psacAssertAccept);
    
  tuple[EventCompatibility incompatible, EventCompatibility sieReject, list[str] allEvents, SpecInfo info] resultReject = 
    runPsacAssertAndIterateModels(l, smtAssert = psacAssertDecline);
  
  println(l);
  printSieResults(resultAccept, resultReject);
}