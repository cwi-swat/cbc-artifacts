module psac::tests::SyntaxBug

import lang::Syntax;
import lang::CommonSyntax;
import lang::ExtendedSyntax;
//import lang::smtlib25::AST;
import IO;
import ParseTree;

import lang::Builder;
import psac::Analysis;
import Set;
//import analysis::PreProcessor;
import psac::Preprocess;

//Formula translateLit((Literal)`<String s>`) = translateLit(s);

//Formula translateLit(String s) = lit(strVal(extractContent(s))) when bprintln("<s>");

str extractContent(String s) = "<s.content>";

//public lang::CommonSyntax::Literal s = (Literal)`"abc"`;

//test bool stringTest() = "<s.content>" == "abc";

//test bool translateTest() = translateLit(s) == lit(strVal("abc"));

loc onUsCreditTransferLoc = |project://ing-specs/src/booking/sepa/ct/OnUsCreditTransfer.ebl|;

test bool stringTest() {
  builts = loadSpecWithImports(onUsCreditTransferLoc);
  Built builtori = getFirstFrom(builts);
  iprintToFile(|project://rebel-sco/target/builtori.txt|, builtori); 
  Built built = preprocess(builtori);
  iprintToFile(|project://rebel-sco/target/built.txt|, built); 
  Module m = built.inlinedMod;
  //Tree t = m;
  //iprintln(t);
  iprintToFile(|project://rebel-sco/target/debug.txt|, m); 
  if(/String s := m) {
    Tree t = s;
    iprintln(t);
    //extractContent(s);
  };
  return false;
}