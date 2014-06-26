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
	| create(loc id, loc constructor, loc actualParameters)
	| assign(loc id, loc target, loc dependsOn)
	| call(loc id, loc receiver, loc method, loc parameter)
	| lock(loc id, loc lock, loc id)
	| unlock(loc id, loc lock, loc id)
	;
