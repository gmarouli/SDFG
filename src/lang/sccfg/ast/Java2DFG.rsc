module lang::sccfg::ast::Java2DFG

import IO;
import Set;
import List;
import String;
import lang::sccfg::ast::DataFlowLanguage;
import lang::java::m3::TypeSymbol;
import lang::java::jdt::m3::AST;
import lang::sccfg::ast::util::ContainersManagement;
import lang::sccfg::ast::util::EnvironmentManagement;
import lang::sccfg::ast::util::ControlFlowHelpers;

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
		<methodStmts, _, _> = dealWithStmts(m, b, environment(env, (),(),())); 
		
		//lock statements if synchronized
		if(lock != unlocked){
			methodStmts += {Stmt::lock(src, lock, {getIdFromStmt(s) | s <- methodStmts})};
		}
		result+= methodStmts;
	}	
	
	return result;
}

tuple[set[Stmt], set[Stmt], Environment] dealWithStmts(Declaration m , Statement b, Environment env){
	set[Stmt] currentBlock = {};
	set[Stmt] potentialStmt = {};

	top-down-break visit(b) {
		case s:Expression::simpleName(name):{
			potentialStmt += {Stmt::read(s@src, s@decl, writtenBy) | writtenBy <- getVariableDependencies(env,s@decl)};	
		}
		case s:Expression::this():{
			potentialStmt += {Stmt::read(s@src, |java+field:///|+ extractClassName(m@decl)+"/this", emptyId)};	
		}
		case s:Expression::fieldAccess(_,exp,_):{
			<unnestedStmts, nestedRead, env> = dealWithStmts(m, \expressionStatement(exp), env);
			potentialStmt += {Stmt::read(s@src, s@decl, writtenBy) | writtenBy <- getVariableDependencies(env,s@decl)} + {Stmt::read(s@src, s@decl, dependOn) | read(dependOn,_,_) <- nestedRead};	
		}
		case s:Expression::fieldAccess(_,_):{
			potentialStmt += {Stmt::read(s@src, s@decl, writtenBy) | writtenBy <- getVariableDependencies(env,s@decl)};	
		}
		case s:Expression::assignment(lhs,_,rhs): {
			<unnestedStmts, nestedReads, env> = dealWithStmts(m, \expressionStatement(rhs), env);
			currentBlock += nestedReads;
			currentBlock += unnestedStmts;
			if(Expression::arrayAccess(ar, index) := lhs){
				//read the assignments of the right handside
				<unnestedStmtsIndex, nestedReadsIndex, env> = dealWithStmts(m, \expressionStatement(index), env);
				
				nestedReads += nestedReadsIndex;
				currentBlock += unnestedStmtsIndex;
				currentBlock += nestedReadsIndex;
				if(nestedReads == {})
					currentBlock += {Stmt::assign(s@src, ar@decl, emptyId)};
				else{
					currentBlock += {Stmt::assign(s@src, ar@decl, id) | Stmt::read(id, _, _) <- nestedReads}; //have to find the right read
					currentBlock += {Stmt::assign(s@src, ar@decl, id) | Stmt::call(id, _, _) <- nestedReads};	
				}
				env = setVariableDependencies(env, ar@decl, {s@src});
				potentialStmt += {Stmt::read(lhs@src, ar@decl, writtenBy) | writtenBy <- getVariableDependencies(env,ar@decl)};
			}
			else if(simpleExpression(lhs)) {
				//read the assignments of the right handside
				if(nestedReads == {}){
					currentBlock += {Stmt::assign(s@src, lhs@decl, emptyId)};
				}
				else{
					currentBlock += {Stmt::assign(s@src, lhs@decl, id) | Stmt::read(id, _, _) <- nestedReads}; //have to find the right read
					currentBlock += {Stmt::assign(s@src, lhs@decl, id) | Stmt::call(id, _, _, _) <- nestedReads};
				}
				env = setVariableDependencies(env, lhs@decl, {s@src});
				potentialStmt += {Stmt::read(lhs@src, lhs@decl, writtenBy) | writtenBy <- getVariableDependencies(env,lhs@decl)};
			}
		}
		case s:Expression::infix(lhs, operator, rhs):{
			if(operator == "&&" || operator == "||"){
				<unnestedStmts, nestedReads, env> = branching(m, lhs, rhs, env);
				currentBlock += unnestedStmts;
				potentialStmt += nestedReads;
			}
			else{
				fail;
			}
		}
		case s:Expression::postfix(operand, operator):{
			if(operator == "++" || operator == "--"){
				<unnestedStmts, nestedReads, env> = dealWithStmts(m,\expressionStatement(operand), env);
				currentBlock += unnestedStmts;
				potentialStmt += nestedReads;
				currentBlock += {Stmt::assign(s@src, operand@decl, id) | read(id,_,_) <- nestedReads};
				env = setVariableDependencies(env, operand@decl, {s@src});
				potentialStmt += {Stmt::read(operand@src, operand@decl, writtenBy) | writtenBy <- getVariableDependencies(env, operand@decl)};				
			}
			else{
				fail;
			}
		}
		case s:Expression::conditional(cond,ifExpr,elseExpr):{
			<unnestedStmts, nestedReads, env> = dealWithStmts(m, \expressionStatement(cond), env);
			currentBlock += unnestedStmts;
			potentialStmt += nestedReads;
		
			<unnestedStmts,nestedReads, env> = branching(m, ifStmts, elseStmts, env);
			currentBlock += unnestedStmts;
			potentialStmt += nestedReads;
		}
		case s:Expression::methodCall(isSuper,name,args):{
			<unnestedStmts, nestedReads, env> = dealWithStmts(m, \methodCall(isSuper, \this(), name, args), env);
			currentBlock += unnestedStmts;
			potentialStmt += nestedReads;
		}
		case s:Expression::methodCall(isSuper, receiver, name, args):{
			for(arg <- args){
				<unnestedStmts, nestedReads, env> = dealWithStmts(m, expressionStatement(arg), env);
				currentBlock += nestedReads;
				currentBlock += unnestedStmts;
			}
			currentBlock+={Stmt::call(s@src, receiver@decl, s@decl, parameter) | read(parameter, _, _) <- nestedReads};
			currentBlock+={Stmt::call(s@src, receiver@decl, s@decl, parameter) | call(parameter, _, _, _) <- nestedReads};	
		}
		case s:Statement::variable(name,_,rhs): {
			<unnestedStmts, nestedReads, env> = dealWithStmts(m, \expressionStatement(rhs), env);
			currentBlock += unnestedStmts + nestedReads;
			if(nestedReads == {})
				currentBlock += {Stmt::assign(s@src, s@decl, emptyId)};
			else{
				currentBlock += {Stmt::assign(s@src, s@decl, id) | Stmt::read(id, _, _) <- nestedReads}; //have to find the right read
				currentBlock += {Stmt::assign(s@src, s@decl, id) | Stmt::call(id, _, _) <- nestedReads};	
			}
			env = setVariableDependencies(env, s@decl, {s@src});
			potentialStmt = {};
		}
		case s:Statement::synchronizedStatement(expr, stmts):{
			<unnestedStmts, nestedReads, env> = dealWithStmts(m, \expressionStatement(expr), env);
			currentBlock += unnestedStmts + nestedReads;
			vlock = getDeclFromRead(getOneFrom(nestedReads));	
						
			<unnestedStmts, nestedReads, env> = dealWithStmts(m, stmts, env);
			currentBlock += unnestedStmts;
			
			currentBlock += {Stmt::lock(s@src, vlock, {getIdFromStmt(id) | id <- unnestedStmts})};
			
		}	
		case s:Statement::\if(cond,ifStmts):{
			<unnestedStmts, nestedReads, env> = dealWithStmts(m, \expressionStatement(cond), env);
			currentBlock += unnestedStmts + nestedReads;
			
			<unnestedStmts, n, envR> = dealWithStmts(m, ifStmts, env);
			currentBlock += unnestedStmts;
			
			env = mergeEnvironments(env, envR);
		}
		case s:Statement::\if(cond,ifStmts,elseStmts):{
			<unnestedStmts, nestedReads, env> = dealWithStmts(m, \expressionStatement(cond), env);
			currentBlock += unnestedStmts + nestedReads;
		
			<unnestedStmts, nestedReads, envIf> = dealWithStmts(m, ifStmts, env);
			currentBlock += unnestedStmts;
			
			<unnestedStmts, nestedReads, envElse> = dealWithStmts(m, elseStmts, env);
			currentBlock += unnestedStmts;
			
			env = mergeEnvironments(envIf, envElse);
			
		}
		case s:Statement::\switch(exp,body):{
			<unnestedStmts, nestedReads, env> = dealWithStmts(m, \expressionStatement(exp), env);
			currentBlock += unnestedStmts + nestedReads;
			previousHelpingEnvironment = env;
			
			insertingEnv = environment(getCurrentEnvironment(env), (), (), getReturnEnvironment(env));
			currentEnv = insertingEnv;
			exitEnv = environment((),(),(),());
			list[Statement] currentCase = [];
			hasDefault = false;
			for(stmt <- body){
				switch(stmt){
					case \case(_):{
						<unnestedStmts, nestedReads, currentEnv> = dealWithStmts(m, \block(currentCase), currentEnv);
						currentBlock += unnestedStmts;
						currentCase = [];
						
						if(getBreakEnvironment(currentEnv) != ()){
							exitEnv = mergeEnvironmentsInBlock(exitEnv, mergeBreak(currentEnv));
							currentEnv = insertingEnv;
						}
					}
					case  \defaultCase():{
						<unnestedStmts, nestedReads, currentEnv> = dealWithStmts(m, \block(currentCase), currentEnv);
						currentBlock += unnestedStmts;
						currentCase = [];
						
						if(getBreakEnvironment(currentEnv) != ()){
							exitEnv = mergeEnvironmentsInBlock(exitEnv, mergeBreak(currentEnv));
							currentEnv = insertingEnv;
						}
						hasDefault = true;
					}
					default:{
						currentCase += [stmt];
					}
				}
			}
			<unnestedStmts, nestedReads, currentEnv> = dealWithStmts(m, \block(currentCase), currentEnv);	
			currentBlock += unnestedStmts;
			exitEnv = mergeEnvironmentsInBlock(exitEnv, mergeBreak(currentEnv));
			if(hasDefault){
				env = mergeEnvironmentsInBlock(currentEnv,exitEnv);
				env = updateEnvironments(insertingEnv, env);
			}
			else{
				env = mergeEnvironments(insertingEnv, exitEnv);
			}		
			env = resetHelpingEnvironment(env,previousHelpingEnvironment);
		}
		case s:Statement::\while(cond,stmts):{
			
			//executed at least once and added to the env, no branching
			previousHelpingEnvironment = env;
			<unnestedStmts, nestedReads, env> = dealWithStmts(m, \expressionStatement(cond), environment(getCurrentEnvironment(env),(),(),(),getReturnEnvironment(env)));
			currentBlock += unnestedStmts + nestedReads;

			//executed once all the reads and assigns added missing connections to itself
			<unnestedStmts, nestedReads, loopedEnv> = dealWithStmts(m, stmts, env);
			currentBlock += unnestedStmts;
			
			//include continue
			loopedEnv = mergeContinue(loopedEnv);
			
			//running the condition after one loop getting all the connections from statements and continue command
			<unnestedStmts, nestedReads, exitEnv> = dealWithStmts(m, \expressionStatement(cond), loopedEnv);
			currentBlock += unnestedStmts + nestedReads;

			<unnestedStmts, n, loopedEnv> = dealWithStmts(m, stmts, exitEnv);
			currentBlock += unnestedStmts;
			
			exitEnv = mergeBreak(exitEnv);
			
			env = mergeEnvironments(env,exitEnv);
			env = resetHelpingEnvironment(env,previousHelpingEnvironment);
		}
		case s:Statement::\do(stmts,cond):{
		
			previousHelpingEnvironment = env;
			//executed once all the reads and assigns added missing connections to itself
			<unnestedStmts, nestedReads, env> = dealWithStmts(m, stmts, envinronment(getCurrentEnvironment(env),(),(),getReturnEnvironment(env)));
			currentBlock += unnestedStmts;
			
			//include continue
			loopedEnv = mergeContinue(env);
			
			//running the condition after one loop getting all the connections from statements and continue command
			<unnestedStmts, nestedReads, exitEnv> = dealWithStmts(m, \expressionStatement(cond), env);
			currentBlock += unnestedStmts + nestedReads;

			<unnestedStmts, n, loopedEnv> = dealWithStmts(m, stmts, exitEnv);
			currentBlock += unnestedStmts;
			
			exitEnv = mergeBreak(exitEnv);
			
			env = mergeEnvironments(env,exitEnv);
			env = resetHelpingEnvironment(env,previousHelpingEnvironment);
		}
		case s:Statement::\for(initializers, cond, updaters, stmts):{

			previousHelpingEnvironment = env;
			<unnestedStmts, nestedReads, env> = dealWithStmts(m, \block([\expressionStatement(i) | i <- initializers]), envinronment(getCurrentEnvironment(env),(),(),getReturnEnvironment(env)));
			currentBlock += unnestedStmts;
			
			//running the condition after one loop getting all the connections from statements and continue command
			<unnestedStmts, nestedReads, env> = dealWithStmts(m, \expressionStatement(cond), env);
			currentBlock += unnestedStmts + nestedReads;

			//executed once all the reads and assigns added missing connections to itself
			<unnestedStmts, nestedReads, loopedEnv> = dealWithStmts(m, stmts, env);
			currentBlock += unnestedStmts;
			
			//include continue
			loopedEnv = mergeContinue(loopedEnv);
			
			//running the condition after one loop getting all the connections from statements and continue command
			<unnestedStmts, nestedReads, loopedEnv> = dealWithStmts(m, \block([\expressionStatement(u) | u <- updaters]), loopedEnv);
			currentBlock += unnestedStmts;

			//running the condition after one loop getting all the connections from statements and continue command
			<unnestedStmts, nestedReads, exitEnv> = dealWithStmts(m, \expressionStatement(cond), loopedEnv);
			currentBlock += unnestedStmts + nestedReads;

			<unnestedStmts, n, loopedEnv> = dealWithStmts(m, stmts, exitEnv);
			currentBlock += unnestedStmts;
			
			exitEnv = mergeBreak(exitEnv);
			
			env = mergeEnvironments(env,exitEnv);
			env = resetHelpingEnvironment(env,previousHelpingEnvironment);			
		}
		case s:Statement::\continue():{
			return <currentBlock, potentialStmt, addToContinueEnvironment(env)>;
			
		}
		case s:Statement::\break(""):{
			return <currentBlock, potentialStmt, addToBreakEnvironment(env)>;
			
		}
		case s:Statement::\break():{
			//to get the environment of different break statements
			return <currentBlock, potentialStmt, addToBreakEnvironment(env)>;		
		}
		case s:Statement::\return():{
			return <currentBlock, potentialStmt, addToReturnEnvironment(env)>;
		}
		case s:Statement::\return(exp):{
			<unnestedStmts, env, nestedReads, _, _> = dealWithStmts(m, \expressionStatement(cond), env);
			currentBlock += unnestedStmts + nestedReads;
			return <currentBlock, potentialStmt, addToReturnEnvironment(env)>;
		}
	}
	return <currentBlock, potentialStmt, env>;
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
	
private loc getIdFromStmt(Stmt::read(id, _, _)) = id;
private loc getIdFromStmt(Stmt::newAssign(id, _, _, _)) = id;
private loc getIdFromStmt(Stmt::assign(id, _, _)) = id;
private loc getIdFromStmt(Stmt::call(id, _, _, _)) = id;
private loc getIdFromStmt(Stmt::lock(id, _, _)) = id;

private loc getDeclFromRead(Stmt::read(_,decl,_)) = decl;