module lang::sdfg::converter::Java2SDFG

import IO;
import Set;
import List;
import String;
import Relation;

import lang::java::jdt::m3::AST;
import lang::java::m3::TypeSymbol;

import lang::sdfg::ast::SynchronizedDataFlowGraphLanguage;

import lang::sdfg::converter::GatherStmtFromStatements;
import lang::sdfg::converter::GatherStmtFromExpressions;

import lang::sdfg::converter::util::State;
import lang::sdfg::converter::util::Getters;
import lang::sdfg::converter::util::ExceptionManagement;
import lang::sdfg::converter::util::EnvironmentManagement;
import lang::sdfg::converter::util::TypeSensitiveEnvironment;

Program createSDFG(loc project) = createSDFG(createAstsFromEclipseProject(project, true));
Program createSDFG(set[Declaration] asts) {
	decls = getDeclarations(asts);
	stmts = getStatements(asts, decls);
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
	
set[Stmt] getStatements(set[Declaration] asts, set[Decl] decls) {

	initialized = gatherInitializations(asts);
	fieldsPerClass = (c@decl.path : {v@decl | field(t,frags) <- b, v <- frags}| /c:class(name, _, _, b) <- asts);
	inheritingClasses = (c@decl.path : {sc@decl.path | simpleType(sc) <- extends}| /c:class(name, extends, _, b) <- asts);
	
	//Gather all methods and constructors
	allMethods 
		= [ m | /m:Declaration::method(_,_,_,_,_) <- asts]
		+ [Declaration::method(t, n, p, e, empty())[@decl=m@decl][@src = m@src] | /m:Declaration::method(Type t,n,p,e) <- asts]
		+ [Declaration::method(simpleType(simpleName(n)), n, p, e, Statement::block((initialized[extractClassName(m@decl)] ? []) + b))[@decl=m@decl][@src=m@src] | /m:Declaration::constructor(str n,p,e,  Statement::block(b)) <- asts]
		+ [Declaration::method(simpleType(simpleName(n)), n, [], [], block(initialized[c@decl.path] ? []))[@decl=(c@decl)[scheme="java+constructor"] + "<n>()"][@src = c@src] | /c:class(n, _, _, b) <- asts, !(Declaration::constructor(_, _, _, _) <- b)]
	;
	
	//Flatten nested classes
	allMethods = visit(allMethods) {
		case declarationExpression(Declaration::class(_)) => Expression::null()
		case declarationExpression(Declaration::class(_,_,_,_)) => Expression::null()
		case declarationExpression(Declaration::enum(_,_,_,_)) => Expression::null()
		
		case declarationStatement(Declaration::class(_)) => empty()
		case declarationStatement(Declaration::class(_,_,_,_)) => empty()
		case declarationStatement(Declaration::enum(_,_,_,_)) => empty()
	};
	
	set[Stmt] result = {};
	set[loc] volatileFields = {vField | attribute(vField, true) <- decls};

	//Gather exceptions
	for (m:Declaration::method(_, _, _, ex, _) <- allMethods) {
		if(ex != []){
			exceptions[m@decl] = {e@decl.path | e <- ex};
		}
	}
	for (m:Declaration::method(_, _, parameters, ex, b) <- allMethods) {
		set[Stmt] methodStmts = {entryPoint(m@src, m@decl)};
		
		//determine lock
		rel[loc,loc] locks = {};
		for(Decl::method(id, _, l) <- decls){
			if((id.path == m@decl.path) && (l != unlocked)){
				locks += {<m@src, l>};
				methodStmts += {read(m@src, l, emptyId)};
			}
		} 
		//set up environment with parameters and fields
		map[loc, set[loc]] env = ( p@decl : {p@src} | p <- parameters) + ( field : {emptyId} | field <- fieldsPerClass[extractClassName(m@decl)] ? {}) + ( field : {emptyId} | sc <- inheritingClasses[extractClassName(m@decl)] ? {}, field <- fieldsPerClass[sc] ? {});
		map[loc, set[loc]] typesOfParam = index({ <getTypeDeclFromTypeSymbol(p@typ),p@decl> | p <- parameters, isClass(p@typ)});
		map[loc,TypeSensitiveEnvironment] typesOf = ( t : typeEnv(typesOfParam[t],{}) | t <- typesOfParam);
		
		rel[loc,loc] acquireActions = locks;
		FlowEnvironment fenv;
		
		top-down-break visit(b) {
			case Expression e : <methodStmts, _, env, typesOf, acquireActions, _> = gatherStmtFromExpressions(e, env, typesOf, volatileFields, acquireActions, methodStmts);
			case Statement s : <methodStmts, env, typesOf, acquireActions, fenv, _> = gatherStmtFromStatements(s, env, typesOf, volatileFields, acquireActions, methodStmts);
		}
		//return environment
		exitSrc = m@src;
		exitSrc.offset = m@src.offset + m@src.length -1;
		for(<src, l> <- locks){
			methodStmts += addAndUnlock(methodStmts, src, l); 
		}
		methodStmts += addAndLock({exitPoint(exitSrc, m@decl)}, acquireActions + getAcquireActions(getReturnState(fenv)));
		result+= methodStmts;
	}	
	return result;
}

	
private loc determineLock(Declaration method){
	loc lock = unlocked;
	if(synchronized() in  (method@modifiers ? {})){
		if(static() in (method@modifiers ? {})){
			str lockPath = extractClassName(method@decl) + ".class";
			lock = |java+class:///|+lockPath;
		}
		else{
			str lockPath = extractClassName(method@decl) + "/this";
			lock = |java+parameter:///|+lockPath;
		}
	}
	return lock;
}

private map[str, list[Statement]] gatherInitializations(set[Declaration] asts) 
	= (c@decl.path : [expressionStatement(v) | field(t,frags) <- b, v <- frags] | /c:class(name, _, _, b) <- asts);
