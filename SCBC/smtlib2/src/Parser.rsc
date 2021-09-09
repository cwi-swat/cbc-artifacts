module Parser

import ParseTree;
import String;
import IO;

import lang::smtlib25::Syntax;

import vis::ParseTree;
import util::Maybe;

start[Script] parseSmt2(loc file) = checkAmbAndContinue(parse(#start[Script], file));
start[Script] parseSmt2(str x, loc file) = checkAmbAndContinue(parse(#start[Script], x, file));

void renderAmbiguity(Tree t) =
	renderParsetree(a)
	when
		/just(a) := isAmbiguous(t);	


Maybe[Tree] isAmbiguous(Tree script) = just(a)
	when /a:amb(_) := script;

default Maybe[set[Tree]] isAmbiguous(Tree script) = nothing();

private start[Script] checkAmbAndContinue(start[Script] script) {
	if (just(_) := isAmbiguous(script)) {
		println("Ambiguity detected");
	}
	
	return script;
}
