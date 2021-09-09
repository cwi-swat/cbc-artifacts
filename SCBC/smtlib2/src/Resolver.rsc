module Resolver

import lang::smtlib25::Syntax;
import ParseTree;
import util::Maybe;
import IO;

alias Def = rel[str name, loc def];
alias Ref = rel[loc ref, loc def];

alias Refs = tuple[Ref vars];

data Scope = scope(loc region, Def defs, list[Scope] children);

Refs resolve(Script script) {
	Scope decls = resolveVarDeclarations(script);

	Ref vars = resolveVarRefs(script, decls);

	return <vars>;
}

Ref resolveVarRefs(Script script, Scope decls) =
	{<ref@\loc,def> | /ref:(Formula)`<Id name>` := script, just(def) := inScope(ref@\loc, "<name>", decls)};

Scope resolveVarDeclarations(Script script) {
	Scope add(loc region, Def defs, Scope st) {
		newScope = top-down-break visit (st) {
			case scope(region, Def d, list[Scope] children) => scope(region, d + defs, children)
			
			case scope(loc r, Def d, []) => scope(r, d, [scope(region, defs, [])])
				when enclosedIn(region, r)
			
			case scope(loc r, Def d, list[Scope] children) => scope(r, d, [add(region, defs, child) | child <- children])
				when enclosedIn(region, r)

			case s:scope(loc r, _, _) => scope(region, defs, [s])
				when enclosedIn(r, region)
		}
		
		if (newScope == st) {
			newScope = top-down-break visit(st) {
			case scope(loc r, Def d, list[Scope] children) => scope(r, d, children + scope(region, defs, []))
				when enclosedIn(region, r)
			}
		}
		
		return newScope;
	}

	Scope scopes = scope(script@\loc, {}, []);

	// defined in functions, quantifiers and let expressions
	visit(script) {
		case f:(Command)`(define-fun <FunctionId _> (<SortedVar* params>) <Sort _> <Formula _>)`: {
			scopes = add(f@\loc,{<"<var.name>", var@\loc> | /SortedVar var := params}, scopes);
		}
		case f:(Formula)`(forall ( <SortedVar+ params> ) <Formula _>)`: {
			scopes = add(f@\loc,{<"<var.name>", var@\loc> | /SortedVar var := params}, scopes);
		}
		case f:(Formula)`(exists ( <SortedVar+ params> ) <Formula _>)`: {
			scopes = add(f@\loc,{<"<var.name>", var@\loc> | /SortedVar var := params}, scopes);
		}
		case f:(Formula)`(let ( <VarBinding+ bindings> ) <Formula _>)`: {
			scopes = add(f@\loc,{<"<binding.name>", binding@\loc> | /VarBinding binding := bindings}, scopes);
		}
		case f:(DataTypeDefinition)`(<SortId name> <Constructor+ cons>)`: {
		  scopes = add(f@\loc,{<"<constructor.name>", constructor@\loc> | /Constructor constructor := cons}, scopes);
		}
	};
	
		// First add the global definitions
	Def global = 	{<"<name>",const@\loc> | /const:(Command)`(declare-const <Id name> <Sort _>)` := script} +
					{<"<name>",const@\loc> | /const:(Command)`(define-fun <Id name> () <Sort _> <Formula _>)` := script};
					// +
					// {<"<constructor.name>", constructor@\loc> | /constructor:(DataTypeDefinition)`(<SortId name> <Constructor+ cons>)` := script};
					// +
					//{<"<definition.name>", definition@\loc> |
					//    /const:(Command)`(declare-datatypes (<SortId* _>) (<DataTypeDefinition* definitions>))` := script,
					//    /DataTypeDefinition definition := definitions, bprintln(definition.name)};

	scopes = add(script@\loc, global, scopes);

	return scopes;
}

Maybe[loc] inScope(loc ref, str var, Scope scopes) {
	bottom-up visit(scopes) {
		case scope(loc r, Def defs, _): {
			if (enclosedIn(ref, r) && {def} := defs[var]) {
				return just(def);
			}
		}
	}
	
	return nothing();
}


bool enclosedIn(loc inner, loc outer) =
	outer.scheme == inner.scheme &&
	outer.authority == inner.authority &&
	outer.path == inner.path &&
	outer.begin.line <= inner.begin.line &&
	(outer.begin.line == inner.begin.line ? outer.begin.column <= inner.begin.column : true) &&
	outer.end.line >= inner.end.line &&
	(outer.end.line == inner.end.line ? outer.end.column >= inner.end.column : true);
