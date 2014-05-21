module lang::sccfg::ast::Java2DFG

import IO;
import Set;
import List;
import String;
import lang::sccfg::ast::DataFlowLanguage;
import lang::java::m3::TypeSymbol;
import lang::java::jdt::m3::AST;
import lang::sccfg::ast::util::ContainersManagement;

Program createDFG(loc project) = createDFG(createAstsFromEclipseProject(project, true));

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
			str lockPath = substring(method@decl.path,0,findLast(method@decl.path,"/")) + ".class";
			lock = lock+lockPath;
		}
		else{
			str lockPath = substring(method@decl.path,0,findLast(method@decl.path,"/")+1) + "this";
			lock = lock+lockPath;
		}
	}
	return lock;
}

private map[str, list[Statement]] gatherInitializations(set[Declaration] asts) 
	= (c@decl.path : [expressionStatement(v) | field(t,frags) <- b, v <- frags] | /c:class(name, _, _, b) <- asts);

set[Stmt] getStatements(set[Declaration] asts, set[Decl] decls) {

	initialized = gatherInitializations(asts);
	
	allMethods 
		= { m | /m:Declaration::method(_,_,_,_,_) <- asts}
		+ {Declaration::method(t, n, p, e, empty())[@decl=m@decl] | /m:Declaration::method(Type t,n,p,e) <- asts}
		+ {Declaration::method(simpleType(simpleName(n)), n, p, e, Statement::block((initialized[substring(m@decl.path,0,findLast(m@decl.path,"/"))] ? []) + b))[@decl=m@decl] | /m:Declaration::constructor(str n,p,e,  Statement::block(b)) <- asts}
		+ {Declaration::method(simpleType(simpleName(n)), n, [], [], block(initialized[c@decl.path] ? []))[@decl=(c@decl)[scheme="java+constructor"] + "<n>()"] | /c:class(n, _, _, b) <- asts, !(Declaration::constructor(_, _, _, _) <- b)}
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
	for (m:Declaration::method(_, _, parameters, _, b) <- allMethods) {
		//determine lock
		loc lock = unlocked;
		for(Decl::method(id, _, l) <- decls){
			if(id.path == m@decl.path)
				lock = l;
		} 
		//set up environment with parameters
		map[loc, set[loc]] env = ( p@decl : {p@src} | p <- parameters);
		<methodStmts, _> = dealWithStmts(m, b, env); 
		
		//lock statements if synchronized
		if(lock != unlocked){
			methodStmts += {Stmt::lock(src, lock, {getIdFromStmt(s) | s <- methodStmts})};
		}
		result+= methodStmts;
	}	
	
	return result;
}

private tuple[set[Stmt], map[loc,set[loc]], set[Stmt]] dealWithStmts(Declaration m , Statement b, map[loc,set[loc]] env){
	set[Stmt] currentBlock = {};
	set[Stmt] potentialStmt = {};
	top-down-break visit(b) {
		case s:Statement::variable(name,_,rhs): {
			<unnestedStmts,env, nestedReads> = dealWithStmts(m, \expressionStatement(rhs), env);
			currentBlock += nestedReads;
			currentBlock += unnestedStmts;
			if(nestedReads == {})
				currentBlock += {Stmt::assign(s@src, s@decl, emptyId)};
			else{
				currentBlock += {Stmt::assign(s@src, s@decl, id) | Stmt::read(id, _, _) <- nestedReads}; //have to find the right read
				currentBlock += {Stmt::assign(s@src, s@decl, id) | Stmt::call(id, _, _) <- nestedReads};	
			}
			env[s@decl] = {s@src};
			potentialStmt = {};
		}
		case s:Expression::assignment(lhs,_,rhs): {
			<unnestedStmts,env, nestedReads> = dealWithStmts(m, \expressionStatement(rhs), env);
			if(Expression::arrayAccess(ar, index) := lhs){
				//read the assignments of the right handside
				currentBlock += nestedReads;
				currentBlock +=  unnestedStmts;
				<unnestedStmtsIndex,env, nestedReadsIndex> = dealWithStmts(m, \expressionStatement(index), env);
				
				nestedReads += nestedReadsIndex;
				currentBlock += unnestedStmtsIndex;
				currentBlock += nestedReadsIndex;
				if(nestedReads == {})
					currentBlock += {Stmt::assign(s@src, ar@decl, emptyId)};
				else{
					currentBlock += {Stmt::assign(s@src, ar@decl, id) | Stmt::read(id, _, _) <- nestedReads}; //have to find the right read
					currentBlock += {Stmt::assign(s@src, lhs@decl, id) | Stmt::call(id, _, _) <- nestedReads};	
				}
				env[ar@decl] = {s@src};
				potentialStmt += {Stmt::read(s@src, ar@decl, emptyId)};
			}
			else if(simpleExpression(lhs)) {
				//read the assignments of the right handside
				currentBlock += nestedReads;
				currentBlock += unnestedStmts;
				if(nestedReads == {}){
					currentBlock += {Stmt::assign(s@src, lhs@decl, emptyId)};
				}
				else{
					currentBlock += {Stmt::assign(s@src, lhs@decl, id) | Stmt::read(id, _, _) <- nestedReads}; //have to find the right read
					currentBlock += {Stmt::assign(s@src, lhs@decl, id) | Stmt::call(id, _, _, _) <- nestedReads};
				}
				env[lhs@decl] = {s@src};
				potentialStmt += {Stmt::read(s@src, lhs@decl, emptyId)};
			}
		}
		case s:Expression::simpleName(name):{
			potentialStmt += {Stmt::read(s@src, s@decl, emptyId)};	
		}
		case s:Expression::infix(lhs, operator, rhs):{
			if(operator == "&&" || operator == "||"){
				<unnestedStmts, env, nestedReads> = branching(lhs,rhs, env);
				currentBlock += unnestedStmts;
				potentialStmt += nestedReads;
			}
			else{
				<unnestedStmts,env, nestedReads> = dealWithStmts(m, \expressionStatement(lhs), env);
				currentBlock += unnestedStmts;
				potentialStmt += nestedReads;
				<unnestedStmts,env, nestedReads> = dealWithStmts(m, \expressionStatement(rhs), env);
				currentBlock += unnestedStmts;
				potentialStmt += nestedReads;
			}
		}
		case s:Expression::conditional(cond,ifStmts,elseStmts):{
			<unnestedStmts,env, nestedReads> = dealWithStmts(m, \expressionStatement(cond), env);
			currentBlock += unnestedStmts;
			potentialStmt += nestedReads;
		
			<unnestedStmts,env, nestedReads> = branching(ifStmts, elseStmts, env);
			currentBlock += unnestedStmts;
			potentialStmt += nestedReads;
		}
		case s:Expression::methodCall(isSuper,name,args):{
			<unnestedStmts,env, nestedReads> = dealWithStmts(m, \methodCall(isSuper, \this(), name, args), env);
			currentBlock += unnestedStmts;
			potentialStmt += nestedReads;
		}
		case s:Expression::methodCall(isSuper, receiver, name, args):{
			for(arg <- args){
				<unnestedStmts,env, nestedReads> = dealWithStmts(m, expressionStatement(arg), env);
				currentBlock += nestedReads;
				currentBlock += unnestedStmts;
			}
			currentBlock+={Stmt::call(s@src, receiver@decl, s@decl, parameter) | read(parameter, _, _) <- nestedReads};
			currentBlock+={Stmt::call(s@src, receiver@decl, s@decl, parameter) | call(parameter, _, _,_) <- nestedReads};
			
		}
		case s:Statement::\if(cond,ifStmts):{
			<unnestedStmts,env, nestedReads> = dealWithStmts(m, \expressionStatement(cond), env);
			currentBlock += unnestedStmts + nestedReads;
			
			<unnestedStmts,envR, nestedReads> = dealWithStmts(m, ifStmts, env);
			currentBlock += unnestedStmts + nestedReads;
			for(variable <- envR){
				if(variable in env){
					env[variable] = env[variable] + envR[variable];
				}
			}
		}
		case s:Statement::\if(cond,ifStmts,elseStmts):{
			<unnestedStmts,env, nestedReads> = dealWithStmts(m, \expressionStatement(cond), env);
			currentBlock += unnestedStmts + nestedReads;
		
			<unnestedStmts,env, nestedReads> = branching(ifStmts, elseStmts, env);
			currentBlock += unnestedStmts + nestedReads;
		}
	}
	return <currentBlock,env, potentialStmt>;
}

private tuple[set[Stmt], map[loc,set[loc]], set[Stmt]] branching(Statement lhs, Statement rhs, map[loc,set[loc]] env){
	currentBlock = {};
	potentialStmt = {};
	<unnestedStmts,env, nestedReads> = dealWithStmts(m, \expressionStatement(lhs), env);
	currentBlock += unnestedStmts;
	potentialStmt += nestedReads;
				
	<unnestedStmts,envR, nestedReads> = dealWithStmts(m, \expressionStatement(rhs), env);
	currentBlock += unnestedStmts;
	potentialStmt += nestedReads;
	for(variable <- envR){
		if(variable in env){
			env[variable] = env[variable] + envR[variable];
		}
	}
	return <currentBlock, env, potentialStmt>;
}
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
