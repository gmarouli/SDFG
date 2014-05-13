module lang::sccfg::ast::DataFlowLanguage

data Program = program(set[Decl] decls, set[Stmt] statements);

public loc emptyId = |id:///|;
public loc unlocked = |lock:///|;

data Decl 
	= attribute(loc id, bool volatile)
	| method(loc id, list[loc] formalParameters, loc lock)
	| constructor(loc id, list[loc] formalParameters)
	;

data Stmt
	= read(loc id, loc variable, loc writtenBy)
	| localDecl(loc id, loc variable, loc volatile)
	| newAssign(loc id, loc target, loc constructor, list[loc] actualParameters)
	| assign(loc id, loc target, loc dependsOn)
	| call(loc id, loc receiver, loc method, list[loc] actualParameters)
	| lock(loc id, loc lock, set[loc] stmts)
	;
