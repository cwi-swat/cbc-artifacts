module psac::IngSpecsRunner

import psac::Analysis;
//import List;
import IO;
import List;
import String;
import util::Math;

public loc onUsCreditTransferLoc = |project://ing-specs/src/booking/sepa/ct/SieOnUsCreditTransfer.ebl|;
public loc multiCurrencyAccountLoc = |project://ing-specs/src/account/multicurrency/Account.ebl|;
public loc restrictionLoc = |project://ing-specs/src/account/multicurrency/Restriction.ebl|;
public loc interestAgreement = |project://ing-specs/src/account/multicurrency/interestAgreement/InterestAgreement.ebl|;
public loc customInterestAgreement = |project://ing-specs/src/account/multicurrency/interestAgreement/CustomInterestAgreement.ebl|;
public loc oranjeInterestAgreement = |project://ing-specs/src/account/multicurrency/interestAgreement/OranjeInterestAgreement.ebl|;
public loc euriBor = |project://ing-specs/src/account/multicurrency/norm/EuriBor.ebl|;
public loc businessCurrentAccount = |project://ing-specs/src/account/payment/BusinessCurrentAccount.ebl|;
public loc block = |project://ing-specs/src/account/payment/block/Block.ebl|;
public loc depositBlock = |project://ing-specs/src/account/payment/block/DepositBlock.ebl|;
public loc directDebitBlock = |project://ing-specs/src/account/payment/block/DirectDebitBlock.ebl|;
public loc specificDirectDebitBlock = |project://ing-specs/src/account/payment/block/SpecificDirectDebitBlock.ebl|;
public loc withdrawBlock = |project://ing-specs/src/account/payment/block/WithdrawBlock.ebl|;
public loc kwartaalLimiet = |project://ing-specs/src/account/payment/limit/KwartaalLimiet.ebl|;
public loc noLimit = |project://ing-specs/src/account/payment/limit/NoLimit.ebl|;
public loc revolvingWashAccount = |project://ing-specs/src/account/process/RevolvingWashAccount.ebl|;
public loc sepaDirectDebitWashAccount = |project://ing-specs/src/account/process/SepaDirectDebitWashAccount.ebl|;
public loc bankTreasury = |project://ing-specs/src/account/system/BankTreasury.ebl|;
public loc creditTransferBatch = |project://ing-specs/src/booking/sepa/ct/CreditTransferBatch.ebl|;
public loc creditBooking = |project://ing-specs/src/booking/sepa/dd/CreditBooking.ebl|;
public loc debitCreditorBooking = |project://ing-specs/src/booking/sepa/dd/DebitCreditorBooking.ebl|;
public loc directDebit = |project://ing-specs/src/booking/sepa/dd/DirectDebit.ebl|;
public loc notFromUsDebitBooking = |project://ing-specs/src/booking/sepa/dd/NotFromUsDebitBooking.ebl|;
public loc notOnUsDebitBooking = |project://ing-specs/src/booking/sepa/dd/NotOnUsDebitBooking.ebl|;
public loc onUsDebitBooking = |project://ing-specs/src/booking/sepa/dd/OnUsDebitBooking.ebl|;
public loc ingNLAccount = |project://ing-specs/src/booking/sepa/wholesale/ct/IngNLAccount.ebl|;
public loc onUsCreditTransferNL = |project://ing-specs/src/booking/sepa/wholesale/ct/OnUsCreditTransferNL.ebl|;
public loc multipleSepaCT = |project://ing-specs/src/booking/sepa/wholesale/ct/example/MultipleSepaCT.ebl|;
public loc arrangement = |project://ing-specs/src/onepam/Arrangement.ebl|;
public loc bankPayment = |project://ing-specs/src/psd/BankPayment.ebl|;
public loc thirdPartyPayment = |project://ing-specs/src/psd/ThirdPartyPayment.ebl|;

public list[loc] sepaLocs = [
    onUsCreditTransferLoc,
    //multiCurrencyAccountLoc, // function to map
    restrictionLoc, 
    //customInterestAgreement, // function to map
    //oranjeInterestAgreement, // arrays
    //euriBor, // function
    //businessCurrentAccount,
    depositBlock,
    directDebitBlock,
    //specificDirectDebitBlock, // sets
    withdrawBlock,
    kwartaalLimiet,
    noLimit,
    revolvingWashAccount,
    sepaDirectDebitWashAccount,
    bankTreasury,
    creditTransferBatch,
    creditBooking,
    debitCreditorBooking,
    //directDebit, //???
    notFromUsDebitBooking,
    notOnUsDebitBooking,
    onUsDebitBooking,
    ingNLAccount,
    onUsCreditTransferNL,
    multipleSepaCT,
    arrangement,
    bankPayment,
    thirdPartyPayment];

void onUsSIE() { 
  SieResult resultAccept = 
    runPsacAssertAndIterateModels(onUsCreditTransferLoc, smtAssert = psacAssertAccept);
    
  SieResult resultReject = 
    runPsacAssertAndIterateModels(onUsCreditTransferLoc, smtAssert = psacAssertDecline);
  
  printSieResults(resultAccept, resultReject);
}

list[AnalysisResult] allSepa() {
  results = [getResults(l)| l <- sepaLocs ];
    
  for( < l
    , resultAccept
    , resultReject
    , acceptSize
    , rejectSize
    , allEventPairsSize
    , delaySize
    , independencyRatio
    , info
    > <- results) {
    println(l); 
    printSieResults(resultAccept, resultReject);
    
    println("Independent / All ratio: <independencyRatio>");
    
    if(acceptSize + rejectSize > allEventPairsSize) {
      println("WARNING: acceptSize <acceptSize> + rejectSize <rejectSize> \> allEventPairsSize <allEventPairsSize>");
    };
  }
   
  totalsStates = ( 0 | it + info.numberOfStates | <_,_,_,_,_,_,_,_,SpecInfo info> <- results );
  totalsEvents = ( 0 | it + info.numberOfEvents | <_,_,_,_,_,_,_,_,SpecInfo info> <- results );
  totalsEventCombinations = ( 0 | it + allEventPairsSize | <_,_,_,_,_,allEventPairsSize,_,_,_> <- results );
  totalAccept = ( 0 | it + acceptSize| <_,_,_,acceptSize,rejectSize,_,_,_,_> <- results );
  totalReject = ( 0 | it + rejectSize | <_,_,_,acceptSize,rejectSize,_,_,_,_> <- results );
  totalIndependent = ( 0 | it + acceptSize + rejectSize | <_,_,_,acceptSize,rejectSize,_,_,_,_> <- results );
  
  println("Total number of states / events / pairs: <totalsStates> / <totalsEvents> / <totalsEventCombinations>");
  println("Total number of independent accept event pairs: <totalAccept>");
  println("Total number of independent reject event pairs: <totalReject>");
  println("Total number of independent event pairs: <totalIndependent>");
  
  println("Percentage independent: <toReal(totalIndependent) / toReal(totalsEventCombinations) * 100>%");
  
  
  
  maskedSpecs = [stringChar(n+65) | n <- [0..size(results)]];
  
  resultsWithMask = zip(results, maskedSpecs);
  
  // tex output
  for( < < l
    , resultAccept
    , resultReject
    , acceptSize
    , rejectSize
    , allEventPairsSize
    , delaySize
    , independencyRatio
    , SpecInfo info
    >, mask> <- resultsWithMask) {
    println("<replaceLast(l.file, ".ebl", "")> & <info.numberOfStates> / <info.numberOfEvents> / <allEventPairsSize> & <acceptSize> & <rejectSize> & <precision(independencyRatio,3)>\\% \\tabularnewline"); 
  }
   
  return results;
}


//void onUsSIE() { 
//  tuple[EventCompatibility incompatible, EventCompatibility sieAccept, list[str] allEvents] resultAccept = 
//    runPsacAssertAndIterateModels(onUsCreditTransferLoc, smtAssert = psacAssertAccept);
//    
//  tuple[EventCompatibility incompatible, EventCompatibility sieReject, list[str] allEvents] resultReject = 
//    runPsacAssertAndIterateModels(onUsCreditTransferLoc, smtAssert = psacAssertDecline);
//  
//  printSieResults(resultAccept, resultReject);
//}

public loc warehouseLoc = |project://rebel-sco/examples/tpc_c/Warehouse.ebl|;
public loc districtLoc = |project://rebel-sco/examples/tpc_c/District.ebl|;
public loc customerLoc = |project://rebel-sco/examples/tpc_c/Customer.ebl|;
public loc historyLoc = |project://rebel-sco/examples/tpc_c/History.ebl|;
public loc orderLoc = |project://rebel-sco/examples/tpc_c/Order.ebl|;
public loc newOrderLoc = |project://rebel-sco/examples/tpc_c/NewOrder.ebl|;
public loc orderLineLoc = |project://rebel-sco/examples/tpc_c/OrderLine.ebl|;
public loc stockLoc = |project://rebel-sco/examples/tpc_c/Stock.ebl|;
public loc itemLoc = |project://rebel-sco/examples/tpc_c/Item.ebl|;

void tpccAnalysis(loc location) { 
  tuple[EventCompatibility incompatible, EventCompatibility sieAccept, list[str] allEvents, SpecInfo info] resultAccept = 
    runPsacAssertAndIterateModels(location, smtAssert = psacAssertAccept);
    
  tuple[EventCompatibility incompatible, EventCompatibility sieReject, list[str] allEvents, SpecInfo info] resultReject = 
    runPsacAssertAndIterateModels(location, smtAssert = psacAssertDecline);
  
  println(location);
  printSieResults(resultAccept, resultReject);
}

alias AnalysisResult = tuple[ loc l
                            , SieResult resultAccept
                            , SieResult resultReject
                            , int acceptSize, int rejectSize, int allEventPairsSize, int delaySize, real independencyRatio
                            , SpecInfo info];

//@memo
AnalysisResult getResults(loc l) {
  SieResult resultAccept = 
    runPsacAssertAndIterateModels(l, smtAssert = psacAssertAccept);
  SieResult resultReject = 
    runPsacAssertAndIterateModels(l, smtAssert = psacAssertDecline);
    
  acceptSize = size(resultAccept.compatible);
  rejectSize = size(resultReject.compatible);
  allEventPairsSize = size(resultAccept.allEvents * resultAccept.allEvents);
  delaySize = allEventPairsSize - acceptSize - rejectSize;
    
  return < l
    , resultAccept
    , resultReject
    , acceptSize
    , rejectSize
    , allEventPairsSize
    , allEventPairsSize - acceptSize - rejectSize
    , toReal(acceptSize + rejectSize) / allEventPairsSize * 100
    , resultAccept.info
    >;
}

void allTpcc() {
  locs = {warehouseLoc, districtLoc, customerLoc, historyLoc, orderLoc, newOrderLoc, orderLineLoc, stockLoc, itemLoc};

  results = {
   getResults(l)| l <- locs };
    
  for( < l
    , resultAccept
    , resultReject
    , acceptSize
    , rejectSize
    , allEventPairsSize
    , delaySize
    , independencyRatio
    , info
    > <- results) {
    println(l); 
    printSieResults(resultAccept, resultReject);
    
    println("Independent / All ratio: <independencyRatio>");
    
    if(acceptSize + rejectSize > allEventPairsSize) {
      println("WARNING: acceptSize <acceptSize> + rejectSize <rejectSize> \> allEventPairsSize <allEventPairsSize>");
    };
  }
  
  totalsEventCombinations = ( 0 | it + allEventPairsSize | <_,_,_,_,_,allEventPairsSize,_,_,_> <- results );
  totalAccept = ( 0 | it + acceptSize| <_,_,_,acceptSize,rejectSize,_,_,_,_> <- results );
  totalReject = ( 0 | it + rejectSize | <_,_,_,acceptSize,rejectSize,_,_,_,_> <- results );
  totalIndependent = ( 0 | it + acceptSize + rejectSize | <_,_,_,acceptSize,rejectSize,_,_,_,_> <- results );
  
  println("Total number of event pairs: <totalsEventCombinations>");
  println("Total number of independent accept event pairs: <totalAccept>");
  println("Total number of independent reject event pairs: <totalReject>");
  println("Total number of independent event pairs: <totalIndependent>");
  
  println("Percentage independent: <toReal(totalIndependent) / toReal(totalsEventCombinations) * 100>%");
  
  
  // tex output
  for( < l
    , resultAccept
    , resultReject
    , acceptSize
    , rejectSize
    , allEventPairsSize
    , delaySize
    , independencyRatio
    , SpecInfo info
    > <- results) {
    //println("<l.file> & <info.numberOfStates> / <info.numberOfEvents> / <allEventPairsSize> & <acceptSize> & <rejectSize> & <toReal(acceptSize + rejectSize) / allEventPairsSize * 100>\\% \\tabularnewline");
    println("<replaceLast(l.file, ".ebl", "")> & <info.numberOfStates> / <info.numberOfEvents> & <acceptSize> / <rejectSize> & <precision(independencyRatio,3)>\\% \\tabularnewline");  
  }
}

// util
str getSieLetter(EventCompatibility accept, EventCompatibility reject, str e1, str e2) {
  str retVal = "";
  if(<e1,e2> <- accept) {
    retVal += "A";
  }
  if(<e1,e2> <- reject) {
    retVal +=  "R";
  } 
  if(<e1,e2> notin accept, <e1,e2> notin reject) {
    retVal +=  "D";
  }
  return retVal;
}

void printSieResults(SieResult resultAccept,
 SieResult resultReject) {
  println("SIE^Accept size:<size(resultAccept.compatible)>, SIE^Reject size:<size(resultReject.compatible)>, Delays: <size(resultAccept.allEvents * resultAccept.allEvents) - size(resultAccept.compatible) - size(resultReject.compatible)>");
  
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

