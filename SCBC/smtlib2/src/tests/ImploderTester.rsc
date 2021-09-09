module tests::ImploderTester

import Parser;
import Imploder;

import ParseTree;
import IO;

import String;

import lang::smtlib25::AST;

bool implodeAllExampleFiles() {
	loc exampleDir = |project://smtlib2/examples|;
	
	for (loc file <- exampleDir.ls) {
		try {
			Tree pt = parseSmt2(file);
			Script scripts = implodeSmt2(pt);
		} catch ex: {
			println("Somthing went wrong during imploding: <file>");
			println("<ex>");
			
			return false;
		}
	}
	
	return true;
}

Script implodeSpecificFile(loc file) {
	Tree pt = parseSmt2(file);
	return implodeSmt2(pt);
}