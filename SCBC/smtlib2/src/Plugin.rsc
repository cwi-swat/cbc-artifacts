module Plugin

import util::IDE;
import ParseTree;
import vis::ParseTree;
import IO;
import Message;
import String;

import Parser;
import Resolver;
import Checker;
import lang::smtlib25::Syntax;

import \solve::Z3;

alias LangDescription = tuple[str name, str ext];

alias PID = int;

anno rel[loc, loc] Tree@hyperlinks;

void main() {
	LangDescription desc = <"SMT2-Lib", "smt2">;
	registerLanguage(desc.name, desc.ext, parseSmt2);
	
	Script lastParsedTree = (Script)``; 
	
	contribs = {
		annotator(&T<:Tree (&T<:Tree scripts) {  
      		lastParsedTree = scripts.top;
      		Refs refs = resolve(scripts.top);
      		set[Message] checkerMessages = check(scripts.top, refs);
      		
      		return scripts[@hyperlinks=refs.vars][@messages=checkerMessages];
    	}),
    	syntaxProperties(#start[Script]),
    	popup(
    		menu("SMT-LIB v2", [
    			toggle("Visualise ambiguity", bool() { return just(_) := isAmbiguous(lastParsedTree); }, 
    				void(Tree tree, loc selection) { renderAmbiguity(tree);}
    			),
    			action("Visualise parse tree", void(Tree tree, loc selection) {
    				renderParsetree(tree.top);	
    			}),
    			action("Run solver", void(Tree tree, loc selection) {
    				runInSolver(tree);
    			})
    		])
    	) 
    };
    
    registerContributions(desc.name, contribs);
}

private void runInSolver(&T<:Tree tree) {
	if (/Script script := tree) { 
		PID pid = startZ3();
		list[str] result = [answer | command <- script.commands, str answer := run(pid, "<command>"), answer != "", answer != "/n"];
		stopZ3(pid);
		
		println("\nAnswer:");
		for (line <- result) {
			println(line);
		}
	}
	else {
		throw "ParseTree not of type Script";
	}		
}
