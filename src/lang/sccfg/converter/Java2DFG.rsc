module lang::sccfg::converter::Java2DFG

import IO;
import Set;
import List;
import String;
import lang::sccfg::ast::DataFlowLanguage;
import lang::java::m3::TypeSymbol;
import lang::java::jdt::m3::AST;
import lang::sccfg::converter::util::ContainersManagement;
import lang::sccfg::converter::util::EnvironmentManagement;
import lang::sccfg::converter::util::ControlFlowHelpers;
import lang::sccfg::converter::GatherStmtFromExpressions;
import lang::sccfg::converter::GatherStmtFromStatements;

Program createDFG(loc project) = createDFG(createAstsFromEclipseProject(project, true));

public map[loc, set[str]] exceptions = ();

Program createDFG(set[Declaration] asts) {
	println("Getting decls");
	decls = getDeclarations(asts);
	println("Getting stmts");
	stmts = getStatements(asts,decls);
	return program(decls, stmts);
}

set[Decl] getDeclarations(set[Declaration] asts) 
	= { Decl::attribute(v@decl,(volatile() in (f@modifiers ? {}))) | /f:field(t,frags) <- asts, v <- frags}
	+ { Decl::method(m@decl, [p@decl | p:parameter(t,_,_) <- params], determineLock(m)) | /m:Declaration::method(_,_, list[Declaration] params, _, _)  <- asts}
	+ { Decl::method(m@decl, [p@decl | p:parameter(t,_,_) <- params], determineLock(m)) | /m:Declaration::method(_,_, list[Declaration] params, _)  <- asts}
	+ { Decl::constructor(c@decl, [p@decl | p:parameter(t,_,_) <- params]) | /c:Declaration::constructor(_, list[Declaration] params, _,_)  <- asts}      
	// add implicit constructor
	+ { Decl::constructor((c@decl)[scheme="java+constructor"] + "<name>()", []) | /c:class(name, _, _, b) <- asts, !(Declaration::constructor(_, _, _, _) <- b)}   
	;
	
private loc determineLock(Declaration method){
	loc lock = unlocked;
	if(synchronized() in  (method@modifiers ? {})){
		if(static() in (method@modifiers ? {})){
			str lockPath = extractClassName(method@decl) + ".class";
			lock = lock+lockPath;
		}
		else{
			str lockPath = extractClassName(method@decl) + "/this";
			lock = lock+lockPath;
		}
	}
	return lock;
}

private map[str, list[Statement]] gatherInitializations(set[Declaration] asts) 
	= (c@decl.path : [expressionStatement(v) | field(t,frags) <- b, v <- frags] | /c:class(name, _, _, b) <- asts);

set[Stmt] getStatements(set[Declaration] asts, set[Decl] decls) {

	initialized = gatherInitializations(asts);
	fieldsPerClass = (c@decl.path : {v@decl | field(t,frags) <- b, v <- frags}| /c:class(name, _, _, b) <- asts);
	inheritingClasses = (c@decl.path : {sc@decl.path | simpleType(sc) <- extends}| /c:class(name, extends, _, b) <- asts);
	
	allMethods 
		= [ m | /m:Declaration::method(_,_,_,_,_) <- asts]
		+ [Declaration::method(t, n, p, e, empty())[@decl=m@decl] | /m:Declaration::method(Type t,n,p,e) <- asts]
		+ [Declaration::method(simpleType(simpleName(n)), n, p, e, Statement::block((initialized[extractClassName(m@decl)] ? []) + b))[@decl=m@decl] | /m:Declaration::constructor(str n,p,e,  Statement::block(b)) <- asts]
		+ [Declaration::method(simpleType(simpleName(n)), n, [], [], block(initialized[c@decl.path] ? []))[@decl=(c@decl)[scheme="java+constructor"] + "<n>()"] | /c:class(n, _, _, b) <- asts, !(Declaration::constructor(_, _, _, _) <- b)]
	;

	allMethods = fixCollections(allMethods);
	
	allMethods = visit(allMethods) {
		case declarationExpression(Declaration::class(_)) => Expression::null()
		case declarationExpression(Declaration::class(_,_,_,_)) => Expression::null()
		case declarationExpression(Declaration::enum(_,_,_,_)) => Expression::null()
		
		case declarationStatement(Declaration::class(_)) => empty()
		case declarationStatement(Declaration::class(_,_,_,_)) => empty()
		case declarationStatement(Declaration::enum(_,_,_,_)) => empty()
	};
	
	set[Stmt] result = {};
	for (m:Declaration::method(_, _, _, ex, _) <- allMethods) {
		if(ex != []){
			exceptions[m@decl] = {e@decl.path | e <- ex};
		}
	}
	for (m:Declaration::method(_, _, parameters, ex, b) <- allMethods) {
		
		//determine lock
		lrel[loc,loc] locks = [];
		for(Decl::method(id, _, l) <- decls){
			if((id.path == m@decl.path) && (l != unlocked))
				locks += [<m@src, l>];
		} 
		//set up environment with parameters and fields
		map[loc, set[loc]] env = ( p@decl : {p@src} | p <- parameters) + ( field : {emptyId} | field <- fieldsPerClass[extractClassName(m@decl)] ? {}) + ( field : {emptyId} | sc <- inheritingClasses[extractClassName(m@decl)] ? {}, field <- fieldsPerClass[sc] ? {});
		set[Stmt] methodStmts = {};
		
		top-down-break visit(b) {
			case Expression e : <methodStmts, _, env, _> = gatherStmtFromExpressions(m, e, env, locks, methodStmts);
			case Statement s : <methodStmts, env, _, _> = gatherStmtFromStatements(m, s, env, locks, methodStmts);
		}
		
		result+= methodStmts;
	}	
	return result;
}

public str extractClassName(loc method) 
	= substring(method.path,0,findLast(method.path,"/"));
	
loc getIdFromStmt(Stmt::read(id, _, _)) = id;
loc getIdFromStmt(Stmt::create(id, _, _)) = id;
loc getIdFromStmt(Stmt::assign(id, _, _)) = id;
loc getIdFromStmt(Stmt::call(id, _, _, _)) = id;
loc getIdFromStmt(Stmt::lock(id, _, _)) = id;

loc getVarFromStmt(Stmt::read(_, var, _)) = var;
loc getVarFromStmt(Stmt::create(_, var, _)) = var;
loc getVarFromStmt(Stmt::assign(_, var, _)) = var;
loc getVarFromStmt(Stmt::call(_, var, _, _)) = var;
loc getVarFromStmt(Stmt::lock(_, var, _)) = var;

private loc getDeclFromRead(Stmt::read(_,decl,_)) = decl;