module tests::ResolverTester

import Resolver;
import Parser;
//import Imploder;
import lang::Syntax;

import ParseTree;
import IO;

void testResolve(loc file) {
	Script script = parseSmt2(file).top;
	//Script scripts = implodeSmt2(pt);
	
	Refs refs = resolve(script);
	//println(refs);
}