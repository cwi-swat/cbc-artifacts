module cbc::Analysis

import lang::ExtendedSyntax;
import lang::Builder;
import lang::smtlib25::AST;
import lang::smtlib25::Compiler;
import solver::SolverRunner;
import Parser;
import analysis::CommonAnalysisFunctions;
import analysis::PreProcessor;
import psac::Preprocess;

import ParseTree;
import String;
import Message;
import IO;
import Set;
import DateTime;

public loc accountLoc = |project://rebel-core/examples/simple_transaction/Account.ebl|;

public loc transactionLoc = |project://rebel-core/examples/simple_transaction/Transaction.ebl|;

set[Built] loadSpecWithImports(loc source) {
 tuple[set[Message] msg, set[Built] builts] loadResult = loadAll(source);
 
  if (loadResult.msg != {}) {
    println("WARNING! There are errors in the modules: <loadResult.msg>");
  }
 
 if(!(isEmpty(loadResult.builts))) {
    specNames = [ "<b.inlinedMod.modDef>" | b <- loadResult.builts];
    println("loaded <specNames>");
    
    //iprintln(compile(translateEntityFrameFunctions(loadResult.builts)));
    return loadResult.builts;
  } else {
    throw "<loadResult.msg>";
  }
}

// States
// >m = analysis();
set[str] getUniqueFroms(LifeCycle l) = { "<s.from>", "<sTo.to>" | /StateFrom s := l, /StateTo sTo := l };
list[str] getStates(Specification spc) = [ capitalize("<f>") | f <- getUniqueFroms(spc.lifeCycle) ];

Command generateStateLabels(Module m) {
  //println("generateStateLabels(Module m)");
  //println(m);
  states = getStates(m.spec);
  list[Constructor] constructors = [cons(s) | s <- states];
  return declareDataTypes([], [dataTypeDef("StateLabel", constructors)]);
}

// Events
list[tuple[str eventName, list[tuple[str fieldName, Sort fieldType]] fields]] extractEvents(EventDefs defs) =
  [ <capitalize("<ev.name>"),  generateTransitionParameters(ev.transitionParams)> | ev <- defs.events ];

list[tuple[str fieldName ,Sort fieldType]] generateTransitionParameters({Parameter ","}* cfg) = [ <"<c.name>", translateSort(c.tipe)> | /Parameter c := cfg ];

//str getMappedType((Type)`set [<Type subType>]`) = "Set[<getMappedType(subType)>]";
str getMappedType((Type)`IBAN`) = "Iban";
//str getMappedType((Type)`Date`) = "DateTime"; // nscala / jodatime
str getMappedType((Type)`Money`) = "Money";
//str getMappedType((Type)`Time`) = "LocalTime";
str getMappedType((Type)`Integer`) = "Int";
//str getMappedType((Type)`DateTime`) = "DateTime";
str getMappedType((Type)`Boolean`) = "Boolean";
str getMappedType((Type)`String`) = "String";
str getMappedType((Type)`Percentage`) = "Real";
str getMappedType((Type)`Long`) = "Int";
//str getMappedType((Type)`map[<Type keyType> : <Type valueType>]`) = "Map[<getMappedType(keyType)>, <getMappedType(valueType)>]";
default str getMappedType(node n) {
    throw "Unable to convert type for node <n>";
}

Command generateEventDataType(Module m) {
  events = extractEvents(m.spec.events);
  
  list[Constructor] constructors = 
  [ combinedCons(e.eventName, vars) 
  | e <- events, list[SortedVar] vars := [ sortedVar("<uncapitalize(e.eventName)>-<var.fieldName>", var.fieldType) | var <- e.fields ] 
  ];

// TODO try to parse this again.
  return declareDataTypes([], [dataTypeDef("Event", constructors)]); //[Command]"(declare-datatypes () ((Event <constructor>)))";
}

Command defineDateOperator(str operator) = defineFunction(operator, [sortedVar("d1", custom("Date")), sortedVar("d2", custom("Date"))], \bool(),
  or([
    functionCall(simple(operator), [functionCall(simple("year"), [var(simple("d1"))]), functionCall(simple("year"), [var(simple("d2"))])]),
    and([
      functionCall(simple("="), [functionCall(simple("year"), [var(simple("d1"))]), functionCall(simple("year"), [var(simple("d2"))])]),
      functionCall(simple(operator), [functionCall(simple("month"), [var(simple("d1"))]), functionCall(simple("month"), [var(simple("d2"))])])
    ]),
    and([
      functionCall(simple("="), [functionCall(simple("year"), [var(simple("d1"))]), functionCall(simple("year"), [var(simple("d2"))])]),
      functionCall(simple("="), [functionCall(simple("month"), [var(simple("d1"))]), functionCall(simple("month"), [var(simple("d2"))])]),
      functionCall(simple(operator), [functionCall(simple("date"), [var(simple("d1"))]), functionCall(simple("date"), [var(simple("d2"))])])
      ])
   ]));

//(define-fun >= ( (d1 Date) (d2 Date)) Bool
//  (or (= d1 d2) (>  (year  d1) (year  d2))))
Command defineDateGeq = defineFunction("\>=", [sortedVar("d1", custom("Date")), sortedVar("d2", custom("Date"))], \bool(),
  or([
    functionCall(simple("="), [var(simple("d1")), var(simple("d2"))]),
    functionCall(simple("\>"), [var(simple("d1")), var(simple("d2"))])
  ]));
Command defineDateLeq = defineFunction("\<=", [sortedVar("d1", custom("Date")), sortedVar("d2", custom("Date"))], \bool(),
  or([
    functionCall(simple("="), [var(simple("d1")), var(simple("d2"))]),
    functionCall(simple("\<"), [var(simple("d1")), var(simple("d2"))])
  ]));

// (define-fun date ((i Int)) Int i)
list[Command] rebelSmtPrelude = declareRebelTypes() 
  + defineFunction("date", [sortedVar("i", \int())], \int(), var(simple("i")))
  //(define-fun + ( (s1 String) (s2 String)) String (str.++ s1 s2))
  + defineFunction("+", [sortedVar("s1", \string()), sortedVar("s2", \string())], \string(), 
      functionCall(simple("str.++"), [var(simple("s1")), var(simple("s2"))]))
      
      // (define-fun > ( (d1 Date) (d2 Date)) Bool (> (date d1) (date d2)))
  + defineDateOperator("\>") + defineDateOperator("\<") + defineDateGeq + defineDateLeq
  ;
    //var(simple("i")));
// defineFunction("date", [defineSort("i", [], \int()), \int(), ]);
//[
//  defineSort("Money", [], \int()),
//  defineSort("Iban", [], \string()),
//  defineSort("Percentage", [], \int())
//  ];

str stateDefName = "State";
  
Command generateState(Fields fields) {
 //(declare-datatypes () ((State (State (label StateLabel) (balance Int)))))
 
  list[tuple[str fieldName, Sort fieldType]] nameAndType = [ <"<f.name>", translateSort(f.tipe)> | f <- fields.fields ];
 
  sortedVars = [ sortedVar(nt.fieldName, nt.fieldType) | nt <- nameAndType];
 
  return declareDataTypes([], [dataTypeDef("State", [combinedCons(stateDefName, [sortedVar("label", custom("StateLabel")), sortedVar("now", \int())] + sortedVars)])]);
}

@memo
lrel[str eventName, str fromState, str toState] stateMap(Specification spc) =
  [ <("<via>"), capitalize("<from.from>"), capitalize("<to.to>")> 
  | StateFrom from <- spc.lifeCycle.from, StateTo to <- from.destinations, /VarName via := to.via];


//Statement trick(Statement s) = visit(s) {
  //case (Expr)`new this.<VarName field>` => (Expr)`post_state.<VarName field>`
  //case new(Expr e) => e when bprintln(e)
//} when bprintln(s);

list[Command] generateEventFunctions(Built built, map[loc, Type] resolvedTypes, map[str,str] specLookup) {
  list[Command] retVal = [];
  spec = built.inlinedMod.spec;
  for(/EventDef ed := spec) {
    str eventName = "<ed.name>";
    //in correct state
    //valid states 
    //println(stateMap(spec));
    //println(eventName);
    validStates = stateMap(spec)[eventName];
    
    str preStateName = "param_this"; // to be compatible by rebel-core SMT translation
    str postStateName = "param_post_state";
    
    // ====
    // preconditions
    list[Formula] stateCheck = [ functionCall(is(state.fromState), [functionCall(simple("label"), [var(simple(preStateName))])])
                               | tuple[str fromState, str toState] state <- validStates ];   
    list[Formula] preChecks = [ translateStat(s, eventAsFunction(specLookup = specLookup, types = resolvedTypes)) 
                              | /Preconditions preconditions := ed, s <- preconditions.stats ];
    params = [sortedVar("param_<p.name>", translateSort(p.tipe)) | p <- ed.transitionParams];
    Command pre = defineFunction("pre_<eventName>", [sortedVar(preStateName, custom("State"))] + params, \bool(), and([or(stateCheck)] + preChecks));
    retVal += pre; 
    
    // postconditions
    list[Formula] stateTransition = [ functionCall(is(state.toState), [functionCall(simple("label"), [var(simple(postStateName))])])
                               | tuple[str fromState, str toState] state <- validStates ];     
    list[Formula] postChecks = [ translateStat(s, eventAsFunction(specLookup = specLookup, types = resolvedTypes)) 
                               | /Postconditions postconditions := ed, s <- postconditions.stats]; //, sWithPostState := trick(s) ];
            
    // find 'new this.<field>', and ignore those for frame conditions                    
    set[str] fieldNamesSetInPostconditions = { "<field>" | /Postconditions postconditions := ed, /(Expr)`new this.<VarName field>` := ed};
    //println("fieldNamesSetInPostconditions: <fieldNamesSetInPostconditions>");
    list[Formula] postFrameConditions = [ lang::smtlib25::AST::eq(
                                            functionCall(simple(fName), [var(simple(preStateName))]),
                                            functionCall(simple(fName), [var(simple(postStateName))]))
                                        | /Fields fields := spec, f <- fields.fields, fName := "<f.name>"
                                        , fName notin fieldNamesSetInPostconditions
                                        //, bprintln("keeping <fName>")
                                        ];                        
    //  (= (now param_post_state) (+ (now param_this) 1))
    Formula advanceTime = lang::smtlib25::AST::eq(functionCall(simple("now"), [var(simple(postStateName))]),
        add(
           functionCall(simple("now"), [var(simple(preStateName))]),
           [lit(intVal(1))]));
    Command post = defineFunction("post_<eventName>", 
      [sortedVar(preStateName, custom(stateDefName)), sortedVar(postStateName, custom(stateDefName))] + params,
      \bool(), and(stateTransition + postChecks + postFrameConditions + advanceTime));
    retVal += post;
  }
  
  // generic methods 
  
  // pre generic
  Formula eventFormula = var(simple("event"));
  Formula preAlternatives = ( lit(boolVal(false)) 
     | ite(functionCall(is(capitalize("<ed.name>")), [eventFormula]), functionCall(simple("pre_<ed.name>"), [var(simple("pre_state"))] + params), it) 
     | /EventDef ed := spec,
       params := [functionCall(simple("<ed.name>-<p.name>"), [eventFormula]) | Parameter p <- ed.transitionParams]
     );

  retVal += defineFunction("pre", [sortedVar("event", custom("Event")), sortedVar("pre_state", custom("State"))], \bool(), preAlternatives);
  
  // post generic
  Formula postAlternatives = ( lit(boolVal(false)) 
     | ite(functionCall(is(capitalize("<ed.name>")), [eventFormula]), functionCall(simple("post_<ed.name>"), [var(simple("pre_state")), var(simple("post_state"))] + params), it) 
     | /EventDef ed := spec,
       params := [functionCall(simple("<ed.name>-<p.name>"), [eventFormula]) | Parameter p <- ed.transitionParams]
     );

  retVal += defineFunction("post", [sortedVar("event", custom("Event")), sortedVar("pre_state", custom("State")), sortedVar("post_state", custom("State"))], \bool(), postAlternatives);
  
  // combined
  retVal += defineFunction("event", 
    [sortedVar("event", custom("Event")), sortedVar("pre_state", custom("State")), sortedVar("post_state", custom("State"))], \bool(), 
    and([functionCall(simple("pre"), [eventFormula, var(simple("pre_state"))]),
         functionCall(simple("post"), [eventFormula, var(simple("pre_state")), var(simple("post_state"))])
        ]));
  
  
  return retVal;
}

bool runInZ3(str smt) {
  int z3 = startSolver();
  try {
//    //println(z3);
//    
    result = runSolver(z3,  smt);
//    //result = isSatisfiable(z3, smt);
//    
    bool sat = checkSat(z3);
//    
    //println("check-sat: <sat>");
    //println(getSolvingTime(z3));
    return sat;
  } catch ex: throw (ex);
  finally {
    stopSolver(z3);
  }
  return false;
}

str translateToSmt(Built mainBuilt, set[Built] builts) {
  println("Picked " + "<mainBuilt.inlinedMod.modDef>");
  
  if(/SpecModifier s := mainBuilt.inlinedMod) {
    throw "Unsupported specifications: <mainBuilt.inlinedMod.modDef> because defined as <s>";
  };
  
  // move IsInit and CheckState's to sync block  
  built = preprocess(mainBuilt);
  Module m = built.inlinedMod;
  
  stateLabels = generateStateLabels(m);
  events = generateEventDataType(m);
  
  // functions
  println("Using <[ "<b.inlinedMod.modDef>" | b <- builts]>");
  PreProcessorResult ppr = preprocess(builts);
  // from Rebel core
  // some extra vars to be able to reuse Joukes code
  //set[Built] specs = {built}; // for now weird set, to keep compatibility with original Rebel code
  //set[Module] specs = {b.normalizedMod | Built b <- {built}};
  map[str,str] specLookup = ("<modul.modDef.fqn.modName>":"<modul.modDef.fqn>" | b <- builts, modul := b.inlinedMod);
  //map[loc, Type] resolvedTypes = (() | it + b.resolvedTypes | Built b <- specs);
  map[loc, Type] resolvedTypes = // loaded.resolvedTypes + 
    (() | it + b.resolvedTypes | Built b <- builts);
  
  list[FunctionDef] funDefs = ppr.functions;
  list[Command] functions = translateFunctions(funDefs, function(types = resolvedTypes));
  
  //println(parseSmt2(compile(events), |project:///|));  
  
  list[Command] smtCommands = rebelSmtPrelude + functions + [stateLabels, events];
  //println(typeOf(m.spec.optFields));
  if(/Fields f := m.spec) {
    smtCommands += generateState(f);
  };
  
  smtCommands += generateEventFunctions(built, resolvedTypes, specLookup);
  
  str smtCode = intercalate("\n", [compile(c) | c <- smtCommands]);
  
  //println(smtCode);
 
  // dump to file
  println("Writing SMT code to file target/last-output-smt.smt2");
  writeFile(|project://rebel-sco/target/last-output-smt.smt2|, smtCode);  
  
  // try parse again, should not throw
  println("Parsing SMT code to check for errors");
  parseSmt2(smtCode, |project:///|);
  
  // try to load in Z3
  println("Try loading SMT code in Z3");
  runInZ3(smtCode);
  
  //println("<script>");
  
  return smtCode;
}

public str sieAssert = "(declare-const e1 Event)
         '(declare-const e2 Event)
         '(declare-const state_post_e1 State)
         '(declare-const state_before State)
         '(assert (not (=\> (event e1 state_before state_post_e1)
         '             (= (pre e2 state_before) (pre e2 state_post_e1))
         ')))";
         
public str sieAssertAccept = "(declare-const e1 Event)
         '(declare-const e2 Event)
         '(declare-const state_post_e1 State)
         '(declare-const state_before State)
         '(declare-const some_state State)
         '(assert (pre e2 some_state))
         '(assert (not (=\> (and (event e1 state_before state_post_e1))
         '             (and (pre e2 state_before) (pre e2 state_post_e1))
         ')))";
         
public str sieAssertDecline = "(declare-const e1 Event)
         '(declare-const e2 Event)
         '(declare-const state_post_e1 State)
         '(declare-const state_before State)
         '(declare-const some_state State)
         '(assert (pre e2 some_state))
         '(assert (not (=\> (and (event e1 state_before state_post_e1))
         '             (and (not (pre e2 state_before)) (not (pre e2 state_post_e1)))
         ')))";
         
//// SIE with commutativity
//public str sieAcceptSer = "(declare-const e1 Event)
//         '(declare-const e2 Event)
//         '(declare-const state_post_e1 State)
//         '(declare-const state_before State)
//         '(declare-const some_state State)
//         '(assert (pre e2 some_state))
//
//         '(declare-const state_post_e2 State)         
//         '(declare-const state_post_e1_e2 State)
//         '(declare-const state_post_e2_e1 State)
//         '(assert (not (=\> (and (event e1 state_before state_post_e1))
//         '             (and (pre e2 state_before) (pre e2 state_post_e1)
//         '     				      (=\> (and (post e2 state_before state_post_e2) (post e2 state_post_e1 state_post_e1_e2) (post e1 state_post_e2 state_post_e2_e1))
//                                 (= state_post_e1_e2 state_post_e2_e1)
//         ' 			       ))
//         ')))";
         
str debugAsserts = "(declare-const pre_e1_before Bool)
                   '(declare-const pre_e2_before Bool)
                   '(declare-const pre_e2_post_e1 Bool)
                   '
                   '(assert (= pre_e1_before (pre e1 state_before)))
                   '(assert (= pre_e2_before (pre e2 state_before)))
                   '(assert (= pre_e2_post_e1 (pre e2 state_post_e1)))";
         
str getNameFromResponse(Expr e) = "<e.constructor>" when e is cons;
str getNameFromResponse(Expr e) = "<e.varName>" when e is var;
str getNameFromResponse(Expr e) = "<e.lit>" when e is lit;
         
alias EventCompatibility = lrel[str,str];
     
Built getBuilt(set[Built] builts, loc specificationLoc) = b when /Built b := builts, bprintln("<b.inlinedMod@\loc.top>"), b.inlinedMod@\loc.top == specificationLoc.top;
     
alias SpecInfo = tuple[loc l, set[str] eventNames, set[str] stateNames, int numberOfEvents, int numberOfStates];
alias SieResult = tuple[EventCompatibility incompatible, EventCompatibility compatible, list[str] allEvents, SpecInfo info];

str runSolverAndLog(SolverPID z3, str smt, loc fileLoc) {
  appendToFile(fileLoc, smt + "\n");
  result = runSolver(z3, smt);
  appendToFile(fileLoc, ";; <result>\n");
  return result;
}

bool checkSatAndLog(SolverPID z3, loc fileLoc) {
  appendToFile(fileLoc, "(check-sat)\n");
  result = checkSat(z3);
  appendToFile(fileLoc, ";; <result?"sat":"unsat">\n");
  return result;
}
     
//@memo
SieResult runAssertAndIterateModels(loc specificationLoc, str smtAssert = sieAssert) {
  set[Built] builts = loadSpecWithImports(specificationLoc);
  Built built = getBuilt(builts, specificationLoc);
  
  //println("built file");
  smt = translateToSmt(built, builts);
  println("translated to SMT");
  int z3 = startSolver();
  enableParallel(z3);
  try {
    println(z3);
    
    str fileName = specificationLoc.file;
    loc fileLoc = |project://rebel-sco/target/<fileName>.smt2|;
    writeFile(fileLoc, ""); // clear file contents  
    writeFile(|project://rebel-sco/target/last-output-smt-assert.smt2|, smt + "\n" + smtAssert);  
    
    runSolverAndLog(z3, smt, fileLoc);  
    runSolverAndLog(z3, smtAssert, fileLoc);
    runSolverAndLog(z3, "(push) ; push definition + asserts", fileLoc); 
    //runSolver(z3, debugAsserts);
    
    list[tuple[str,str, list[str]]] incompatibleEvents = [];
    
    allEvents = { capitalize("<ed.name>") | /EventDef ed := built.inlinedMod.spec };
    combinations = { <e1,e2> | e1 <- allEvents, e2 <- allEvents};
    
    for(<E1,E2> <- combinations) {
      asserts = "(assert (and (is-<E1> e1) (is-<E2> e2)))";
      runSolverAndLog(z3, asserts, fileLoc);
      
      println("<now()> Checking: <E1>, <E2>:");
      bool sat = checkSatAndLog(z3, fileLoc);
      //println("check-sat: <sat>");
      //println(getSolvingTime(z3));
    
      if(sat) {
        println("Counter example found for <E1>, <E2>: <intercalate( " ", [ "\t<m> <model[m]>"  | model := getModel(z3, ["e1", "e2"]), m <- model ])>");
       
        model = getModel(z3, ["e1", "e2", "s0", "s01", "s02", "s012", "s021"]);
        println("\t model: <intercalate( " ", [ "\t<m> <model[m]>"  | m <- model ])>");
       
             
        e1 = getValue(z3, "e1");
        e2 = getValue(z3, "e2");
        incompatibleEvents += <getNameFromResponse(e1), getNameFromResponse(e2), [ "\t<m> <model[m]>"  | m <- model]>;
      }
      // continue
      runSolverAndLog(z3, "(pop) (push)", fileLoc); 
    }
    //println("\<in progress event, incoming event e\>");
    //println("incompatibleEvents: <intercalate("\n", incompatibleEvents)>");
    
    //println(combinations);
    plainIncompatibleEvents = { <e1,e2> | <e1,e2,_> <- incompatibleEvents };
    //println(plainIncompatibleEvents);
    set[tuple[str,str]] compatibleEvents = combinations - plainIncompatibleEvents;
    //println(compatibleEvents);
    
    //println("\<compatible: in progress event, incoming event e\>");
    //println("<intercalate("\n", toList(compatibleEvents))>");
    //println("\<[counter examples], [compatible events with assert]\>");
    allStates = getStates(built.inlinedMod.spec);
    SpecInfo specInfo = <specificationLoc, allEvents, toSet(allStates), size(allEvents), size(allStates)>;
    return <sort(plainIncompatibleEvents), sort(compatibleEvents), sort(allEvents), specInfo>;
    } catch ex: throw (ex);
  finally {
    println("Stopping solver <z3>");
    stopSolver(z3);
  }
}

//quickScalaConverter(runPsacAssertAndIterateModels(accountLoc, smtAssert = psacAssertDecline).compatible, "failFastEvents"))
//quickScalaConverter(runPsacAssertAndIterateModels(accountLoc, smtAssert = psacAssertAccept).compatible, "alwaysCompatibleEvents"))
str quickScalaConverter(EventCompatibility ec, str functionName) =
  "override def <functionName>: PartialFunction[(Event, Event), Boolean] = {" +
     intercalate("\n", [ "  case (_: <e1>, _: <e2>) =\> true" | <e1, e2> <- ec]) +
  "\n}";