module Checker

import Resolver;
import lang::smtlib25::Syntax;

import Message;
import ParseTree;

set[Message] check(Script script, Refs refs) =
	checkVarRefs(script, refs);
	
set[Message] checkVarRefs(Script script, Refs refs) =
	{error("Referenced constant \'<name>\' can not be found", v@\loc) | /v:(Formula)`<Id name>` := script, refs.vars[v@\loc] == {}};