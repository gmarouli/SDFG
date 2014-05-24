module lang::sccfg::ast::Java2DFG

import IO;
import Set;
import List;
import String;
import lang::sccfg::ast::DataFlowLanguage;
import lang::java::m3::TypeSymbol;
import lang::java::jdt::m3::AST;
import lang::sccfg::ast::util::ContainersManagement;
import  lang::sccfg::ast::util::ControlFlowHelpers;

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
	fieldsPerClass = ( c@decl.path : {v@decl | field(t,frags) <- b, v <- frags}| /c:class(name, _, _, b) <- asts);

	allMethods 
		= { m | /m:Declaration::method(_,_,_,_,_) <- asts}
		+ {Declaration::method(t, n, p, e, empty())[@decl=m@decl] | /m:Declaration::method(Type t,n,p,e) <- asts}
		+ {Declaration::method(simpleType(simpleName(n)), n, p, e, Statement::block((initialized[extractClassName(m@decl)] ? []) + b))[@decl=m@decl] | /m:Declaration::constructor(str n,p,e,  Statement::block(b)) <- asts}
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
		//set up environment with parameters and fields
		map[loc, set[loc]] env = ( p@decl : {p@src} | p <- parameters) + ( field : {emptyId} | field <- fieldsPerClass[extractClassName(m@decl)]);
		<methodStmts, _, _> = dealWithStmts(m, b, env); 
		
		//lock statements if synchronized
		if(lock != unlocked){
			methodStmts += {Stmt::lock(src, lock, {getIdFromStmt(s) | s <- methodStmts})};
		}
		result+= methodStmts;
	}	
	
	return result;
}

private tuple[set[Stmt], map[loc,set[loc]], set[Stmt], map[loc,set[loc]], map[loc,set[loc]]] dealWithStmts(Declaration m , Statement b, map[loc,set[loc]] env){
	set[Stmt] currentBlock = {};
	set[Stmt] potentialStmt = {};
	map[loc,set[loc]] potentialContinueEnv = ();
	map[loc,set[loc]] potentialBreakEnv = ();
	top-down-break visit(b) {
		case s:Expression::simpleName(name):{
			potentialStmt += {Stmt::read(s@src, s@decl, writtenBy) | writtenBy <- env[s@decl]};	
		}
		case s:Expression::assignment(lhs,_,rhs): {
			<unnestedStmts,env, nestedReads, _, _> = dealWithStmts(m, \expressionStatement(rhs), env);
			if(Expression::arrayAccess(ar, index) := lhs){
				//read the assignments of the right handside
				currentBlock += nestedReads;
				currentBlock +=  unnestedStmts;
				<unnestedStmtsIndex,env, nestedReadsIndex, _, _> = dealWithStmts(m, \expressionStatement(index), env);
				
				nestedReads += nestedReadsIndex;
				currentBlock += unnestedStmtsIndex;
				currentBlock += nestedReadsIndex;
				if(nestedReads == {})
					currentBlock += {Stmt::assign(s@src, ar@decl, emptyId)};
				else{
					currentBlock += {Stmt::assign(s@src, ar@decl, id) | Stmt::read(id, _, _) <- nestedReads}; //have to find the right read
					currentBlock += {Stmt::assign(s@src, ar@decl, id) | Stmt::call(id, _, _) <- nestedReads};	
				}
				env[ar@decl] = {s@src};
				potentialStmt += {Stmt::read(lhs@src, ar@decl, writtenBy) | writtenBy <- env[ar@decl]};
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
				potentialStmt += {Stmt::read(lhs@src, lhs@decl, writtenBy) | writtenBy <- env[lhs@decl]};
			}
		}
		case s:Expression::infix(lhs, operator, rhs):{
			if(operator == "&&" || operator == "||"){
				<unnestedStmts, env, nestedReads, _, _> = branching(lhs,rhs, env);
				currentBlock += unnestedStmts;
				potentialStmt += nestedReads;
			}
			else{
				<unnestedStmts,env, nestedReads, _, _> = dealWithStmts(m, \expressionStatement(lhs), env);
				currentBlock += unnestedStmts;
				potentialStmt += nestedReads;
				<unnestedStmts,env, nestedReads, _, _> = dealWithStmts(m, \expressionStatement(rhs), env);
				currentBlock += unnestedStmts;
				potentialStmt += nestedReads;
			}
		}
		case s:Expression::conditional(cond,ifExpr,elseExpr):{
			<unnestedStmts,env, nestedReads, _, _> = dealWithStmts(m, \expressionStatement(cond), env);
			currentBlock += unnestedStmts;
			potentialStmt += nestedReads;
		
			<unnestedStmts,env, nestedReads, _, _> = branching(ifStmts, elseStmts, env);
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
		case s:Statement::variable(name,_,rhs): {
			<unnestedStmts,env, nestedReads, _, _> = dealWithStmts(m, \expressionStatement(rhs), env);
			currentBlock += unnestedStmts + nestedReads;
			if(nestedReads == {})
				currentBlock += {Stmt::assign(s@src, s@decl, emptyId)};
			else{
				currentBlock += {Stmt::assign(s@src, s@decl, id) | Stmt::read(id, _, _) <- nestedReads}; //have to find the right read
				currentBlock += {Stmt::assign(s@src, s@decl, id) | Stmt::call(id, _, _) <- nestedReads};	
			}
			env[s@decl] = {s@src};
			potentialStmt = {};
		}
		case s:Statement::\if(cond,ifStmts):{
			<unnestedStmts,env, nestedReads, _, _> = dealWithStmts(m, \expressionStatement(cond), env);
			currentBlock += unnestedStmts + nestedReads;
			
			<unnestedStmts,envR, n, continueEnv, breakEnv> = dealWithStmts(m, ifStmts, env);
			currentBlock += unnestedStmts;
			potentialContinueEnv = mergeInBlockEnvironments(continueEnv,potentialContinueEnv);
			potentialBreakEnv = mergeInBlockEnvironments(breakEnv,potentialBreakEnv);
			
			env = mergeEnvironments(env, envR);
		}
		case s:Statement::\if(cond,ifStmts,elseStmts):{
			<unnestedStmts,env, nestedReads, _, _> = dealWithStmts(m, \expressionStatement(cond), env);
			currentBlock += unnestedStmts + nestedReads;
		
			<unnestedStmts,env, nestedReads, continueEnv, breakEnv> = branching(ifStmts, elseStmts, env);
			currentBlock += unnestedStmts;
			potentialContinueEnv = mergeInBlockEnvironments(continueEnv,potentialContinueEnv);
			potentialBreakEnv = mergeInBlockEnvironments(breakEnv,potentialBreakEnv);
			
		}
		case s:Statement::\while(cond,stmts):{
			
			//executed at least once and added to the env, no branching
			<unnestedStmts,env, nestedReads, _, _> = dealWithStmts(m, \expressionStatement(cond), env);
			currentBlock += unnestedStmts + nestedReads;

			//executed once all the reads and assigns added missing connections to itself
			<unnestedStmts, loopedEnv, nestedReads, continueEnv, breakEnv> = dealWithStmts(m, stmts, env);
			currentBlock += unnestedStmts;
			
			//include continue
			loopedEnv = mergeInBlockEnvironments(loopedEnv, continueEnv);
			
			//running the condition after one loop getting all the connections from statements and continue command
			<unnestedStmts, exitEnv, nestedReads, _, _> = dealWithStmts(m, \expressionStatement(cond), loopedEnv);
			currentBlock += unnestedStmts + nestedReads;

			<unnestedStmts, loopedEnv, n, _, _> = dealWithStmts(m, stmts, exitEnv);
			currentBlock += unnestedStmts;
			
			exitEnv = mergeInBlockEnvironments(exitEnv,breakEnv);
			
			env = mergeEnvironments(env,exitEnv);
		}
		case s:Statement::\do(stmts,cond):{

			//executed once all the reads and assigns added missing connections to itself
			<unnestedStmts, env, nestedReads, continueEnv, breakEnv> = dealWithStmts(m, stmts, env);
			currentBlock += unnestedStmts;
			
			//include continue
			loopedEnv = mergeInBlockEnvironments(env, continueEnv);
			
			//running the condition after one loop getting all the connections from statements and continue command
			<unnestedStmts, exitEnv, nestedReads, _, _> = dealWithStmts(m, \expressionStatement(cond), env);
			currentBlock += unnestedStmts + nestedReads;

			<unnestedStmts, loopedEnv, n, _, _> = dealWithStmts(m, stmts, exitEnv);
			currentBlock += unnestedStmts;
			
			exitEnv = mergeInBlockEnvironments(exitEnv,breakEnv);
			
			env = mergeEnvironments(env,exitEnv);
		}
		case s:Statement::\for(initializers, cond, updaters, stmts):{

			<unnestedStmts, env, nestedReads, _, _> = dealWithStmts(m, \block([\expressionStatement(i) | i <- initializers]), env);
			currentBlock += unnestedStmts;
			
			//running the condition after one loop getting all the connections from statements and continue command
			<unnestedStmts, env, nestedReads, _, _> = dealWithStmts(m, \expressionStatement(cond), env);
			currentBlock += unnestedStmts + nestedReads;

			//executed once all the reads and assigns added missing connections to itself
			<unnestedStmts, loopedEnv, nestedReads, continueEnv, breakEnv> = dealWithStmts(m, stmts, env);
			currentBlock += unnestedStmts;
			
			//include continue
			loopedEnv = mergeInBlockEnvironments(loopedEnv, continueEnv);
			
			//running the condition after one loop getting all the connections from statements and continue command
			<unnestedStmts, loopedEnv, nestedReads, _, _> = dealWithStmts(m, \block([\expressionStatement(u) | u <- updaters]), loopedEnv);
			currentBlock += unnestedStmts;

			//running the condition after one loop getting all the connections from statements and continue command
			<unnestedStmts, exitEnv, nestedReads, _, _> = dealWithStmts(m, \expressionStatement(cond), loopedEnv);
			currentBlock += unnestedStmts + nestedReads;

			<unnestedStmts, loopedEnv, n, _, _> = dealWithStmts(m, stmts, exitEnv);
			currentBlock += unnestedStmts;
			
			exitEnv = mergeInBlockEnvironments(exitEnv,breakEnv);
			
			env = mergeEnvironments(env,exitEnv);
		}
		case s:Statement::\continue():{
			potentialContinueEnv = mergeInBlockEnvironments(env,potentialContinueEnv);
		}
		case s:Statement::\break(""):{
			potentialBreakEnv = mergeInBlockEnvironments(env,potentialBreakEnv);
		}
		case s:Statement::\break():{
			potentialBreakEnv = mergeInBlockEnvironments(env,potentialBreakEnv);
		}
	}
	return <currentBlock, env, potentialStmt, potentialContinueEnv, potentialBreakEnv>;
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

private str extractClassName(loc method) 
	= substring(method.path,0,findLast(method.path,"/"));
	
