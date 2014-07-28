module lang::sdfg::ast::SynchronizedDataFlowGraphLanguage

data Program = program(set[Decl] decls, set[Stmt] stmts);

public loc emptyId = |id:///|;
public loc unlocked = |lock:///|;
public loc independentValue = |value:///|;

data Decl 
	= attribute(loc id, bool volatile)
	| method(loc id, list[loc] formalParameters, loc lock)
	| constructor(loc id, list[loc] formalParameters)
	;

data Stmt
	= read(loc id, loc variable, loc dataDepId)
	| assign(loc id, loc variable, loc dataDepId)
	| change(loc id, loc typeDecl, loc dataDepId) 
	
	| acquireLock(loc id, loc lock, loc syncDepId)
	| releaseLock(loc id, loc lock, loc syncDepId)
	
	| create(loc id, loc constructor, loc actualParameterId)
	| call(loc id, loc receiver, loc method, loc actualParameterId)

	| entryPoint(loc id, loc method)
	| exitPoint(loc id, loc method)
	;
