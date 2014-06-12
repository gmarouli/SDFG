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

map[loc, set[loc]] exceptions = ();

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
			exceptions[m@decl] = {e@decl | e <- ex};
		}
	}
	println(exceptions);
	for (m:Declaration::method(_, _, parameters, ex, b) <- allMethods) {
		
		//determine lock
		loc lock = unlocked;
		for(Decl::method(id, _, l) <- decls){
			if(id.path == m@decl.path)
				lock = l;
		} 
		//set up environment with parameters and fields
		map[loc, set[loc]] env = ( p@decl : {p@src} | p <- parameters) + ( field : {emptyId} | field <- fieldsPerClass[extractClassName(m@decl)] ? {}) + ( field : {emptyId} | sc <- inheritingClasses[extractClassName(m@decl)] ? {}, field <- fieldsPerClass[sc] ? {});
		<methodStmts, _, _> = visitStatements(m, b, env, (), {});
		//lock statements if synchronized
		if(lock != unlocked){
			methodStmts += {Stmt::lock(m@src, lock, {s | s <- methodStmts})};
		}
		result+= methodStmts;
	}	
	return result;
}


tuple[set[Stmt], map[loc, set[loc]], map[loc, map[loc, set[loc]]]] visitStatements(Declaration m , Statement b, map[loc, set[loc]] env, map[loc, map[loc, set[loc]]] exs, set[Stmt] stmts){
	top-down-break visit(b) {
		case Expression e : <stmts, _, env, exs> = gatherStmtFromExpressions(m, e, env, exs, stmts);
		case Statement s : <stmts, env, _, exs> = gatherStmtFromStatements(m, s, env, flowEnvironment((),()), exs, stmts);
	}
	return <stmts, env, exs>;
}


//	top-down-break visit(b) {
//		case s:Statement::variable(name,_,rhs): {
//			<unnestedStmts, nestedReads, env> = dealWithStmts(m, \expressionStatement(rhs), env);
//			currentBlock += unnestedStmts + nestedReads;
//			if(nestedReads == {})
//				currentBlock += {Stmt::assign(s@src, s@decl, emptyId)};
//			else{
//				currentBlock += {Stmt::assign(s@src, s@decl, id) | Stmt::read(id, _, _) <- nestedReads}; //have to find the right read
//				currentBlock += {Stmt::assign(s@src, s@decl, id) | Stmt::call(id, _, _) <- nestedReads};	
//			}
//			env = setVariableDependencies(env, s@decl, {s@src});
//			potentialStmt = {};
//		}
//		case s:Statement::synchronizedStatement(expr, stmts):{
//			<unnestedStmts, nestedReads, env> = dealWithStmts(m, \expressionStatement(expr), env);
//			currentBlock += unnestedStmts + nestedReads;
//			vlock = getDeclFromRead(getOneFrom(nestedReads));	
//						
//			<unnestedStmts, nestedReads, env> = dealWithStmts(m, stmts, env);
//			currentBlock += unnestedStmts;
//			
//			currentBlock += {Stmt::lock(s@src, vlock, {lockedStmt | lockedStmt <- unnestedStmts})};
//			
//		}	





//		case s:Statement::\try(b,catchStmts):{
//			<unnestedStmts, nestedReads, env> = dealWithStmts(m, b, env);
//			currentBlock += unnestedStmts;
//			println("I am in a try");
//		}
//	}
//	return <currentBlock, potentialStmt, env>;
//}

bool simpleExpression(fieldAccess(_,_,_)) = true;
bool simpleExpression(fieldAccess(_,_)) = true;
bool simpleExpression(qualifiedName(_,e)) = simpleExpression(e);
bool simpleExpression(this()) = true;
bool simpleExpression(this(_)) = true;
bool simpleExpression(simpleName(_)) = true;
default bool simpleExpression(Expression e) = false;

bool isArray(arrayAccess(_,_)) = true;
default bool isArray(e) = false; 

Expression removeNesting(cast(_, e)) = removeNesting(e);
Expression removeNesting(\bracket(e)) = removeNesting(e);
default Expression removeNesting(Expression e) = e;

private str extractClassName(loc method) 
	= substring(method.path,0,findLast(method.path,"/"));
	
loc getIdFromStmt(Stmt::read(id, _, _)) = id;
loc getIdFromStmt(Stmt::create(id, _, _, _)) = id;
loc getIdFromStmt(Stmt::assign(id, _, _)) = id;
loc getIdFromStmt(Stmt::call(id, _, _, _)) = id;
loc getIdFromStmt(Stmt::lock(id, _, _)) = id;

loc getVarFromStmt(Stmt::read(_, var, _)) = var;
loc getVarFromStmt(Stmt::create(_, var, _, _)) = var;
loc getVarFromStmt(Stmt::assign(_, var, _)) = var;
loc getVarFromStmt(Stmt::call(_, var, _, _)) = var;
loc getVarFromStmt(Stmt::lock(_, var, _)) = var;

private loc getDeclFromRead(Stmt::read(_,decl,_)) = decl;