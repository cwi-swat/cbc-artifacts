@license{
  Copyright (c) 2009-2015 CWI
  All rights reserved. This program and the accompanying materials
  are made available under the terms of the Eclipse Public License v1.0
  which accompanies this distribution, and is available at
  http://www.eclipse.org/legal/epl-v10.html
}
@doc{
	Synopsis: Wrapper around the Microsoft Z3 solver. Lets you execute SMT statements (as SMTLIBv2 AST commands) and returns the found answer (if any). 
}
@contributor{Jouke Stoel - stoel@cwi.nl (CWI)}

module solver::Z3

import String;
import IO;
import util::SystemAPI;

import util::ShellExec;

@doc{
	Starts the Z3 solver.
	To run the solver the path to Z3 needs to be configure either by adding the -Dsolver.z3.path=<local.path.to.z3> to your eclipse.ini configuration or by supplying it 
	when you call the solver using the keyword parameter 'pathToZ3'
}
PID startZ3(str pathToZ3 = getSystemProperty("solver.z3.path")) {
  writeFile(smtTraceLoc, ""); // clear file contents  
	pid = createProcess(pathToZ3 == "" ? "/usr/local/bin/z3" : "<pathToZ3>/bin/z3", args = ["-smt2", "-in"]);

	// The print-success option is needed so that each entered statement returns a result. This way we have a predictable inputstream that we can read
	run(pid, "(set-option :print-success true)"); 
	//run(pid, "(set-option :parallel.enable true)"); 
	//run(pid, "(set-option :interactive-mode true)");
	
	return pid;
}

void stopZ3(PID z3) { 
	writeTo(z3, "(exit)\n"); 
	killProcess(z3);
}

loc smtTraceLoc = |project://target/smt-io.smt2|;

str \run(PID z3, str command, bool debug = false) {
  printIfDebug(command, debug);

  smtCommand = "<command>\n";
  appendToFile(smtTraceLoc, smtCommand);
  writeTo(z3, smtCommand); // the \n is added because the outcome of the command will otherwise not be flushed
  str outcome = read(z3);
  
  if (outcome != "") {
    printIfDebug("Answer: <outcome>", debug);
    appendToFile(smtTraceLoc, ";; <outcome>\n");
    
    if (startsWith(outcome, "(error")) {
      throw "Problem with SMT constraints: <outcome>";
    }
  }
  
  return outcome;  
}

public str read(PID z3) {
  result =  replaceAll(replaceAll(readFrom(z3), "success", ""), "\n", "");
  if(!isEmpty(result)) {
    appendToFile(smtTraceLoc, ";; <result>\n");
  }
  return result;
}

private void printIfDebug(str line, bool debug) {
	if (debug) {
		println(line);
	}
}
