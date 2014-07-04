module lang::sccfg::converter::Java2SDFG

import IO;
import Set;
import Relation;
import List;
import String;

import lang::java::jdt::m3::AST;
import lang::java::m3::TypeSymbol;

import lang::sccfg::ast::DataFlowLanguage;

import lang::sccfg::converter::GatherStmtFromStatements;
import lang::sccfg::converter::GatherStmtFromExpressions;

import lang::sccfg::converter::util::Getters;
import lang::sccfg::converter::util::ExceptionManagement;
import lang::sccfg::converter::util::ContainersManagement;
import lang::sccfg::converter::util::TypeSensitiveEnvironment;

Program createDFG(loc project) = createDFG(createAstsFromEclipseProject(project, true));
Program createDFG(set[Declaration] asts) {
	decls = getDeclarations(asts);
	stmts = getStatements(asts, decls);
	iprintToFile(|file:///D:/object_flow_thesisspace/University/OFG/Student.ofg|, program(decls, stmts));
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
	
	allMethods 
		= [ m | /m:Declaration::method(_,_,_,_,_) <- asts]
		+ [Declaration::method(t, n, p, e, empty())[@decl=m@decl][@src = m@src] | /m:Declaration::method(Type t,n,p,e) <- asts]
		+ [Declaration::method(simpleType(simpleName(n)), n, p, e, Statement::block((initialized[extractClassName(m@decl)] ? []) + b))[@decl=m@decl][@src=m@src] | /m:Declaration::constructor(str n,p,e,  Statement::block(b)) <- asts]
		+ [Declaration::method(simpleType(simpleName(n)), n, [], [], block(initialized[c@decl.path] ? []))[@decl=(c@decl)[scheme="java+constructor"] + "<n>()"][@src = c@src] | /c:class(n, _, _, b) <- asts, !(Declaration::constructor(_, _, _, _) <- b)]
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
	set[loc] volatileFields = {vField | attribute(vField, true) <- decls};

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
		map[loc, set[loc]] typesOfParam = index({ <getClassDeclFromType(p@typ),p@decl> | p <- parameters, isClass(p@typ)});
		map[loc,TypeSensitiveEnvironment] typesOf = ( t : typeEnv(typesOfParam[t],{}) | t <- typesOfParam);
		set[Stmt] methodStmts = {entryPoint(m@src, m@decl)};
		lrel[loc,loc] acquireActions = [];
		lrel[loc,loc] actionsInPath = [];
		
		top-down-break visit(b) {
			case Expression e : <methodStmts, _, env, typesOf, actionsInPath, _> = gatherStmtFromExpressions(e, env, typesOf, volatileFields, acquireActions, actionsInPath, methodStmts);
//			case Statement s : <methodStmts, env, _, acquireActions, _> = gatherStmtFromStatements(m, s, env, volatileFields, acquireActions, methodStmts);
		}
		exitSrc = m@src;
		exitSrc.offset = m@src.offset + m@src.length -1;
		methodStmts += addAndLock({exitPoint(exitSrc, m@decl)}, actionsInPath);
		result+= methodStmts;
	}	
	return result;
}

	
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
