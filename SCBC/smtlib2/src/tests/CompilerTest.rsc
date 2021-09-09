module tests::CompilerTest

import Parser;
import Imploder;
import Compiler;
import lang::AST;

import ParseTree;
import IO;
import List;
import String;

void compileOneFile(loc file) {
	Tree pt = parseSmt2(file);
	Script scr = implodeSmt2(pt);
	
	list[str] compiled = toString(scr);
	for (line <- compiled) {
		println(line);
	}
}

bool compileAllFiles() {
	loc exampleDir = |project://smtlib2/examples|;
	
	for (loc file <- exampleDir.ls) {
		try {
			Tree pt = parseSmt2(file);
			Script scr = implodeSmt2(pt);
			list[str] compiled = toString(scr);
			
			if (contains(intercalate(" ", compiled), "unknown command")) {
				throw "Not all construct are translated back to smt lib v2, see file <file>";
			}			
		} catch ex: {
			println("Somthing went wrong during imploding: <file>");
			println("<ex>");
			
			return false;
		}
	}
	
	return true;
}