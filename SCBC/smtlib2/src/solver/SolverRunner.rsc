module solver::SolverRunner

import solver::Z3;

import List;
import String;
//import Boolean;
import IO;
//import Map;
//import lang::smtlib25::Syntax;
import lang::smtlib25::response::Parser;
import lang::smtlib25::response::Syntax;
import util::Sleeper;

alias SolverPID = int;

data ResultUnkownException
  = to() // timeout
  | uk(str reason) // unknown
  ;

SolverPID startSolver() {
  pid = startZ3();
  
  // make sure that the unsatisfiable core are produced
  //runSolver(pid, "(set-option :produce-unsat-cores true)");
  
  return pid;
}

void stopSolver(SolverPID pid) {
  stopZ3(pid);
}

void setTimeOut(SolverPID pid, int timeOutInMs) {
  runSolver(pid, "(set-option :timeout <timeOutInMs>)");
}

void enableParallel(SolverPID pid) {
  runSolver(pid, "(set-option :parallel.enable true)");
}

bool isSatisfiable(SolverPID pid, str smtFormula) { 
  if (smtFormula != "") {
      list[str] smt = split("\n", smtFormula);
      for (s <- smt) {
        str solverResult = trim(runSolver(pid, s)); 
        if (solverResult != "") {
          throw "Unable to assert clauses: <solverResult>"; 
        }   
      }
      
      // do a 'flush'
      runSolver(pid, "\n");
  }
  
  return checkSat(pid);
}

bool checkSat(SolverPID pid) {
  str result = runSolverAndExpectResult(pid, "(check-sat)");
  
  //println(result);
  
  switch(result) {
    case /unsat.*/: return false;
    case /sat.*/ : return true;
    case /unknown.*/: {
      throw getReason(pid);
    }   
    default: throw "unable to get result from smt solver: <result>"; 
  }
}

private ResultUnkownException getReason(SolverPID pid){
  str reason = runSolverAndExpectResult(pid, "(get-info :reason-unknown)");
  println(reason);
  
  if (/.*canceled.*/ := reason || /.*timeout.*/ := reason || /.*resource[ ]limits[ ]reached.*/ := reason) {
    return to();
  } else {
    return uk(reason);
  }  
}

int getSolvingTime(SolverPID pid) {
  str result = runSolverAndExpectResult(pid, "(get-info :all-statistics)");
  //println(result);
  int time = 0;  
  if (/[:]time[ ]*<sec:[0-9]*>[.]<hun:[0-9][0-9]>/ := result) {
    time = toInt(sec)*1000 + toInt(hun[0] == "0" ? hun[1] : hun)*10;  
  } else {
    throw "Unable to parse the solving time from the statistics of Z3";
  }
  
  return time;
}

Expr getValue(SolverPID pid, str vars) = val when {val} := getModel(pid, [vars])<1>;

map[str,Expr] getModel(SolverPID pid, list[str] vars) {
  smtResult = runSolverAndExpectResult(pid, "(get-value (<intercalate(" ", vars)>))");
  //println(smtResult);
  
  Response foundValues = parseResponse(trim(smtResult)); 
  
  map[str,Expr] rawSmtVals = ("<foundValue.var>" : foundValue.val | /FoundValue foundValue := foundValues);
  //map[str,SmtValue] rawSmtVals = (() | it + ("<varAndVal.name>":varAndVal.val) | VarAndValue varAndVal <- foundValues.values);
  //SMTModel m = (var : val | str varName <- rawSmtVals, SMTVar var:<varName, Sort _> <- vars, Term val := getValue(rawSmtVals[varName], var));
  
  return rawSmtVals;
}    

//str runSolverAndExpectResult(SolverPID pid, str commands) { 
//  str result = run(pid,commands, debug=false);
//  
//  str oldResult = result;
//  while (trim(result) == "" || result != oldResult) {
//    try {
//      oldResult = result;
//      sleep(5); 
//      result += read(pid);
//    } catch ex: {
//      println("Exception while SMT solver, reason: <ex>");
//      println("Retrying...");
//    }
//  }
//  
//  return result;
//}
str runSolverAndExpectResult(SolverPID pid, str commands) { 
  str result = run(pid,commands, debug=false);
  while (true) {
    try {
      str oldResult = result;
      sleep(5); 
      result += read(pid);
      if(trim(result) != "" && result == oldResult) {
        return result;
      }
    } catch ex: {
      println("Exception while SMT solver, reason: <ex>");
      println("Retrying...");
    }
  }
  return result;
}

str runSolver(SolverPID pid, str commands) {
  try {
    return run(pid, commands, debug=false);
  }
  catch er: throw "Error while running SMT solver, reason: <er>";   
}