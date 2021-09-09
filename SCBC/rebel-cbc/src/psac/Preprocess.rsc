module psac::Preprocess

import lang::Builder;
//import lang::Syntax;
import lang::ExtendedSyntax;

import IO;
import List;

syntax SyncExpr
  = initialize: Expr e
  // initialize: "initialized" Expr var!accessor "[" Expr indx "]"
  //| "instate" blabla
  ;

// Preprocessor that moved `initialized` and `InState` to sync block
Built preprocess(Built modul) {
  //println("preprocess(Built modul)");
  retVal = visit(modul) {
      // rewrite all event defs, move initalized from pre/post to sync
      case EventDef ed => preprocess(ed)
  };
  
  //println(retVal.inlinedMod);  
  return retVal;
}

EventDef preprocess(EventDef ed) {
    //println("preprocess(EventDef ed)");
    set[SyncStatement] initializeds = 
      { (SyncStatement)`<Annotations annos> <SyncExpr syncExpr>;` 
      | /Statement stat := ed //, bprintln(stat)
      , /expr:(Expr)`initialized <Expr _>` := stat
      , SyncExpr syncExpr := (SyncExpr)`<Expr expr>`
      , annos := stat.annos };
    
    //println("Initializeds: <initializeds>");
    //list[SyncStatement] syncs = [ (SyncStatement)`<Expr x>;` | SyncStatement x <- initializeds];
    //println("<syncs>");
    //return withoutInitializeds;
    syncStrings = intercalate(" ", [ s | s <- initializeds]);
    //println("syncStrings: <syncStrings>");
      
    
    // needed to add to concrete syntax preconditions
    Preconditions addPreconditionStatement(p:(Preconditions)`preconditions { <Statement* statements> }`, Statement newStatement) =
      (Preconditions)`preconditions { <Statement* statements> <Statement newStatement> }`[@\loc=p@\loc];
    default Preconditions addPreconditionStatement(Preconditions block, Statement new) {
      println("did not match <block>+<new>");  
    }
    
    Preconditions addPreconditionStatements(Preconditions sync, set[Statement] newStatements) =
      ( sync 
      | addPreconditionStatement(it, newStatement) 
      | newStatement <- newStatements ); 
      
    EventDef withoutInitializeds = visit(ed) {
      case Preconditions pre => {
         set[Statement] conditionsWithoutInitialized = { statement | /Statement statement := pre, !/(Expr)`initialized <Expr _>` := statement };
         addPreconditionStatements((Preconditions)`preconditions {  }`, conditionsWithoutInitialized);
      } when /(Expr)`initialized <Expr _>` := pre // only rewrite preconditions that actually contain initialized
      //TODO  postconditions
      //case Postconditions post => 
    };
    

    
    //syncBlock = (MaybeSyncBlock)`sync { <SyncStatement* syncs> }`;  // (SyncBlock?)`sync { <SyncStatement* syncs> }`;  // [SyncBlock]"sync { <syncStrings> }";
    MaybeSyncBlock syncBlock = [MaybeSyncBlock]"sync { <syncStrings> }";  // (SyncBlock?)`sync { <SyncStatement* syncs> }`;  // [SyncBlock]"sync { <syncStrings> }";
    //return withoutInitializeds;
    //println(syncBlock);

    //SyncBlock addSyncStatement(orig:(SyncBlock)`sync { <SyncStatement* statements> }`, SyncStatement newStatement) =
    //  (SyncBlock)`sync { <SyncStatement* statements> <SyncStatement newStatement> }`;
    //
    //SyncBlock addSyncStatements(SyncBlock sync, set[SyncStatement] newStatements) =
    //  ( sync 
    //  | addSyncStatement(it, newStatement) 
    //  | newStatement <- newStatements );
  
      
    MaybeSyncBlock addMaybeSyncStatement(s:(MaybeSyncBlock)`sync { <SyncStatement* statements> }`, SyncStatement newStatement) =
      (MaybeSyncBlock)`sync { <SyncStatement* statements> <SyncStatement newStatement> }`[@\loc=s@\loc];
    default MaybeSyncBlock addMaybeSyncStatement(MaybeSyncBlock block, SyncStatement newStatement) = {
      //iprintln(block);
      println("Assume `<block>` is empty since  `(MaybeSyncBlock)`` ` does not seem to match a empty optional"); 
      (MaybeSyncBlock)`sync { <SyncStatement newStatement> }`[@\loc=block@\loc];  
    };
    
    MaybeSyncBlock addMaybeSyncStatements(MaybeSyncBlock sync, set[SyncStatement] newStatements) =
      ( sync 
      | addMaybeSyncStatement(it, newStatement) 
      | newStatement <- newStatements );

    return withoutInitializeds[sync=addMaybeSyncStatements(withoutInitializeds.sync, initializeds)];
    
    //println(retVal);  
    //return retVal;

//if(just(Built b) := loadModule(|project://rebel-core/examples/simple_transaction/Transaction.ebl|), /EventDef ed := b, "<ed.name>" == "start" ) { println(preprocess(ed)); }

    //return visit(withoutInitializeds) {
    //  case EventDef eventDef => eventDef[sync=addMaybeSyncStatements((MaybeSyncBlock)`sync { }`, initializeds)] 
    //    when !(eventDef has sync)
    //  case SyncBlock block => {
    //    println("found" + "<block>");
    //    println("Adding" + "<initializeds>");
    //    addSyncStatements(block, initializeds);
    //    //(SyncBlock)`sync { <SyncStatement* statements> <SyncStatement* syncStrings> }`[@\loc = block@\loc];  //block[stats = syncString] // (SyncBlock)`sync { <SyncStatement* syncString>}`
    //  } when SyncStatement* statements := block.stats //, syncString := [SyncStatement*]"<statements> <syncs>"
    //}
    
    //return withoutInitializeds[sync = (SyncBlock)`sync { <initializeds2> }`] when initializeds2 := initializeds;
  }