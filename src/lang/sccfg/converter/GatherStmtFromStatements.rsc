module lang::sccfg::converter::GatherStmtFromStatements

import IO;
import Set;
import List;
import String;
import lang::sccfg::ast::DataFlowLanguage;
import lang::java::m3::TypeSymbol;
import lang::java::jdt::m3::AST;
import lang::sccfg::converter::util::Getters;
import lang::sccfg::converter::util::ContainersManagement;
import lang::sccfg::converter::util::EnvironmentManagement;
import lang::sccfg::converter::util::ControlFlowHelpers;
import lang::sccfg::converter::GatherStmtFromExpressions;
import lang::sccfg::converter::util::AcquireActionsManagement;

//assert(Expression expression)
tuple[set[Stmt], map[loc,set[loc]], FlowEnvironment, rel[loc,loc], AcquireActionsPaths, map[str, ExceptionState]] gatherStmtFromStatements(Declaration m, Statement s:\assert(exp), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, rel[loc,loc] actionsInPath, set[Stmt] stmts){
	return gatherStmtFromStatements(m, \assert(exp, Expression::null()), env, volatileFields, actionsInPath, stmts);
}

//assert(Expression expression, Expression message)
tuple[set[Stmt], map[loc,set[loc]], FlowEnvironment, rel[loc,loc], AcquireActionsPaths, map[str, ExceptionState]] gatherStmtFromStatements(Declaration m, Statement s:\assert(exp, message), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, rel[loc,loc] actionsInPath, set[Stmt] stmts){
	<stmts, potential, env, exs> = gatherStmtFromExpressions(m, exp, env, volatileFields, acquireActions, actionsInPath, stmts);
	stmts += potential;
	actionsInPath += extractAcquireAction(potential, volatileFields);
	
	<stmts, potential, envM, exsM> = gatherStmtFromExpressions(m, message, env, volatileFields, acquireActions, actionsInPath, stmts);
	stmts += potential;
	actionsInExitPath += extractAcquireAction(potential, volatileFields);
	exs = mergeExceptionState(exs, exsM);
	//the volatile access from the message are not counted since if the message appears nothing else is going to be executed
	//The assert is a possible an exit point, in case of finally we can see it as a return
	env = mergeNestedEnvironment(env,envM);
	return <stmts, env, initializeReturnEnvironment(env), actionsInPath, initializeAcquireActionsFromReturn(actionsInExitPath), exs>;
}

//block(list[Statement] statements)
tuple[set[Stmt], map[loc,set[loc]], FlowEnvironment, rel[loc,loc], AcquireActionsPaths, map[str, ExceptionState]] gatherStmtFromStatements(Declaration m, Statement s:\block(sB), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, rel[loc,loc] actionsInPath, set[Stmt] stmts){
	envInner = env;
	exs = ();
	fenv = emptyFlowEnvironment();
	actionsFromOtherPaths = emptyAcquireActionsPaths();
	for(stmt <- sB){
		<stmts, envInner, fenvS, actionsInPath, actionsFromOtherPathsS, exsS> = gatherStmtFromStatements(m, stmt, envInner, volatileFields, acquireActions, actionsInPath, stmts);
		fenv = mergeFlow(fenv, fenvS);
		exs = mergeExceptionState(exs, exsS);
		actionsFromOtherPaths = mergeActions(actionsFromOtherPaths, actionsFromOtherPathsS);
		if(breakingControlFlow(stmt))
			break;
	}
	env = updateEnvironment(env, envInner);
	return <stmts, env, fenv, actionsInPath, actionsFromOtherPaths, exs>;
}

//break()
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc], AcquireActionsPaths, map[str, ExceptionState]] gatherStmtFromStatements(Declaration m, Statement s:\break(), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, rel[loc,loc] actionsInPath, set[Stmt] stmts){
	return <stmts, env, initializeBreakEnvironment(env), [], initializeAcquireActionsFromBreak(actionsInPath), ()>;
}

//break("")
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc], AcquireActionsPaths, map[str, ExceptionState]] gatherStmtFromStatements(Declaration m, Statement s:\break(""), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, rel[loc,loc] actionsInPath, set[Stmt] stmts){
	// ISSUE: what if break is not in a branch? then it is perceived partly as a continue
	return <stmts, env, initializeBreakEnvironment(env), [], initializeAcquireActionsFromBreak(actionsInPath), ()>;
}

//break(str label)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc], AcquireActionsPaths, map[str, ExceptionState]] gatherStmtFromStatements(Declaration m, Statement s:\break(_), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, rel[loc,loc] actionsInPath, set[Stmt] stmts){
	assert false : "Labeled statement (break) found!!!";
	return <stmts, env, initializeBreakEnvironment(env), [], initializeAcquireActionsFromBreak(actionsInPath), ()>;
}

//continue()
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc], AcquireActionsPaths, map[str, ExceptionState]] gatherStmtFromStatements(Declaration m, Statement s:\continue(), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, rel[loc,loc] actionsInPath, set[Stmt] stmts){
	return <stmts, env, initializeContinueEnvironment(env), [], initializeAcquireActionsFromContinue(actionsInPath), ()>;
}

//continue(str label)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc], AcquireActionsPaths, map[str, ExceptionState]] gatherStmtFromStatements(Declaration m, Statement s:\continue(_), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, rel[loc,loc] actionsInPath, set[Stmt] stmts){
	assert false : "Labeled statement (continue) found!!!";
	return <stmts, env, initializeContinueEnvironment(env), [], initializeAcquireActionsFromContinue(actionsInPath), ()>;
}

//do(Statement body, Expression condition)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc], AcquireActionsPaths, map[str, ExceptionState]] gatherStmtFromStatements(Declaration m, Statement s:\do(b, cond), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, rel[loc,loc] actionsInPath, set[Stmt] stmts){
		
	//executed once all the reads and assigns added missing connections to itself
	<stmts, env, fenvInner, acquireActions, exs> = gatherStmtFromStatements(m, b, env, volatileFields, acquireActions, stmts);
			
	//include continue
	env = mergeNestedEnvironment(env, getContinueEnvironment(fenvInner));
			
	//running the condition after one loop getting all the connections from statements and continue command
	<stmts, potential, env, acquireActions, exsC> = gatherStmtFromExpressions(m, cond, env, volatileFields, acquireActions, stmts);
	exs = mergeExceptionState(exs, exsC);
	stmts += potential;
	acquireActions += extractAcquireActions(potential, volatileFields);
	
	//connect the statements with the condition but the environment and exception are already found
	<stmts, env, _, exsC> = gatherStmtFromStatements(m, b, env, volatileFields, acquireActions, stmts);

	env = mergeNestedEnvironment(env, getBreakEnvironment(fenvInner));
	
	return <stmts, env, initializeReturnEnvironment(getReturnEnvironment(fenvInner)), acquireActions, exs>;
}

//foreach(Declaration parameter, Expression collection, Statement body)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc], AcquireActionsPaths, map[str, ExceptionState]] gatherStmtFromStatements(Declaration m, Statement s:\foreach(parameter, collection, body), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, rel[loc,loc] actionsInPath, set[Stmt] stmts){
	outerEnv = env;
	<stmts, potential, env, exs> = gatherStmtFromExpressions(m, collection, env, volatileFields, acquireActions, stmts);
	stmts += potential;
	acquireActions += extractAcquireActions(potential, volatileFields);
	//this variable is declared locally it cannot be volatile
	stmt += addAndLock({Stmt::assign(s@src, parameter@decl, s@src)}, acquireActions);
	env[parameter@decl] = {s@src};
	
	outerEnv = updateEnvironment(outerEnv, env);
	
	//executed once all the reads and assigns added missing connections to itself
	<stmts, env, fenvInner, exsC> = gatherStmtFromStatements(m, b, env, volatileFields, acquireActions, stmts);
	exs = mergeExceptionState(exs,exsC);		
	//include continue
	env = mergeNestedEnvironment(env, getContinueEnvironment(fenvInner));
			
	//running the condition after one loop getting all the connections from statements and continue command
	<stmts, potential, env, _> = gatherStmtFromExpressions(m, collection, env, volatileFields, acquireActions, stmts);
	stmts += potential;
	
	//connect the statements with the condition but the environment and exception are already found
	<stmts, env, _, _> = gatherStmtFromStatements(m, b, env, volatileFields, acquireActions, stmts);

	env = mergeNestedEnvironment(env, getBreakEnvironment(fenvInner));
	
	return <stmts, mergeNestedEnvironment(outerEnv,env), emptyFlowEnvironment(), acquireActions, exs>;
}

//for(list[Expression] initializers, Expression condition, list[Expression] updaters, Statement body)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc], AcquireActionsPaths, map[str, ExceptionState]] gatherStmtFromStatements(Declaration m, Statement s:\for(initializers, cond, updaters, body), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, rel[loc,loc] actionsInPath, set[Stmt] stmts){
	return dealWithLoopsConditionFirst(m, initializers, cond, updaters, body, env, volatileFields, acquireActions, stmts);
} 

//for(list[Expression] initializers, list[Expression] updaters, Statement body)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc], AcquireActionsPaths, map[str, ExceptionState]] gatherStmtFromStatements(Declaration m, Statement s:\for(initializers, updaters, body), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, rel[loc,loc] actionsInPath, set[Stmt] stmts){
	return dealWithLoopsConditionFirst(m, initializers, Expression::\null(), updaters, body, env, volatileFields, acquireActions, stmts);
}

//expressionStatement(Expression stmt)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc], AcquireActionsPaths, map[str, ExceptionState]] gatherStmtFromStatements(Declaration m, Statement s:\expressionStatement(e), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, rel[loc,loc] actionsInPath, set[Stmt] stmts){
	<stmts, potential, env, actionsInPath, exs> = gatherStmtFromExpressions(m, e, env, volatileFields, acquireActions, actionsInPath, stmts);
	return <stmts, env, emptyFlowEnvironment(), actionsInPath, emptyAcquireActionsPaths(), exs>;
}

//if(Expression condition, Statement thenB)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc], AcquireActionsPaths, map[str, ExceptionState]] gatherStmtFromStatements(Declaration m, Statement s:\if(cond, thenB), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, rel[loc,loc] actionsInPath, set[Stmt] stmts){
	<stmts, potential, env, actionsInPath, exs> = gatherStmtFromExpressions(m, cond, env, volatileFields, acquireActions, actionsInPath, stmts);
	stmts += potential;
	actionsInPath += extractAcquireActions(potential, volatileFields);
	
	<stmts, envOpt, fenv, actionsInPathThen, actionsFromOtherPaths, exsC> = gatherStmtFromStatements(m, thenB, env, volatileFields, acquireActions + actionsInPath, [], stmts);
	exs = mergeExceptionState(exs,exsC);
				

	env = mergeNestedEnvironment(env,envOpt);
	return <stmts, env, fenv, actionsInPath + actionsInPathThen, actionsFromOtherPaths, exs>;
}

//if(Expression condition, Statement thenB, Statement elseB)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc], AcquireActionsPaths, map[str, ExceptionState]] gatherStmtFromStatements(Declaration m, Statement s:\if(cond, thenB, elseB), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, rel[loc,loc] actionsInPath, set[Stmt] stmts){
	<stmts, potential, env, actionsInPath, exs> = gatherStmtFromExpressions(m, cond, env, volatileFields, acquireActions, actionsInPath, stmts);
	stmts += potential;
	actionsInPath += extractAcquireActions(potential, volatileFields);
	
	<stmts, env, fenv, actionsInIfPath, actionsFromOtherPaths, exsC> = branching(m, thenB, elseB, env, volatileFields, acquireActions + actionInPath, [], stmts); 
	return <stmts, env, fenv, actionsInPath + actionsInIfPath, actionsFromOtherPaths, merge(exs, exsC)>;
}

//label(str name, Statement body)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc], AcquireActionsPaths, map[str, ExceptionState]] gatherStmtFromStatements(Declaration m, Statement s:\label(_, _), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, rel[loc,loc] actionsInPath, set[Stmt] stmts){
	assert false: "Labeled block";
	return <stmts, env, emptyFlowEnvironment(), actionsInPath, emptyAcquireActionsPaths(), ()>;
}

//return(Expression expression)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc], AcquireActionsPaths, map[str, ExceptionState]] gatherStmtFromStatements(Declaration m, Statement s:\return(exp), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, rel[loc,loc] actionsInPath, set[Stmt] stmts){
	<stmts, potential, env, actionsInPath, exs> = gatherStmtFromExpressions(m, exp, env, volatileFields, acquireActions, actionsInPath, stmts);
	stmts += potential;
	actionsInPath += extractAcquireActions(potential, volatileFields); //needed for the finally
	return <stmts, env, initializeReturnEnvironment(env), [], initializeAcquireActionsFromReturn(actionsInPath), exs>;
}

//return()
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc], AcquireActionsPaths, map[str, ExceptionState]] gatherStmtFromStatements(Declaration m, Statement s:\return(), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, rel[loc,loc] actionsInPath, set[Stmt] stmts){
	return <stmts, env, initializeReturnEnvironment(env), [], initializeAcquireActionsFromReturn(actionsInPath), exs>;
}

//switch(Expression exp, list[Statement] statements)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc], AcquireActionsPaths, map[str, ExceptionState]] gatherStmtFromStatements(Declaration m, Statement s:\switch(exp, body), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, rel[loc,loc] actionsInPath, set[Stmt] stmts){
	<stmts, potential, env, actionsInPath, exs> = gatherStmtFromExpressions(m, exp, env, volatileFields, acquireActions, actionsInPath, stmts);
	stmts += potential;
	actionsInPath += extractAcquireActions(potential, volatileFields);
	
	outerEnv = env;
	rel[loc,loc] outerAcquireActions = acquireActions + actionsInPath;
	rel[loc,loc] currentAcquireActions = acquireActions + actionsInPath;
	exitEnv = ();
	fenv = emptyFlowEnvironment();
	
	list[Statement] currentCase = [];
	hasDefault = false;
	for(stmt <- body){
		switch(stmt){
			case \case(_):{
				<stmts, currentEnv, fenvInner, currentAcquireActions, exsC> = gatherStmtFromStatements(m, \block(currentCase), currentEnv, volatileFields, currentAcquireActions, stmts);
				acquireActions += currentAcquireActions;
				exs = mergeExceptionState(exs, exsC);
				fenv = mergeFlow(fenv, fenvInner);
				currentCase = [];
						
				if(getBreakEnvironment(fenvInner) != ()){
					exitEnv = merge(exitEnv, getBreakEnvironment(fenvInner));
					currentEnv = outerEnv;
					currentAcquireActions = outerAcquireActions;
				}
				else{
					currentEnv = updateEnvironment(outerEnv, currentEnv);
				}
			}
			case  \defaultCase():{
				hasDefault = true;
				<stmts, currentEnv, fenvInner, currentAcquireActions, exsC> = gatherStmtFromStatements(m, \block(currentCase), currentEnv, volatileFields, currentAcquireActions, stmts);
				acquireActions += currentAcquireActions;
				exs = mergeExceptionState(exs, exsC);
				fenv = mergeFlow(fenv, fenvInner);
				currentCase = [];
							
				if(getBreakEnvironment(fenvInner) != ()){
					exitEnv = merge(exitEnv, getBreakEnvironment(fenvInner));
					currentEnv = outerEnv;
					currentAcquireActions = outerAcquireActions;
				}
				else{
					currentEnv = updateEnvironment(outerEnv, currentEnv);
				}
			}
			default:{
				currentCase += [stmt];
			}
		}
	}

	<stmts, currentEnv, fenvInner, currentAcquireActions, exsC> = gatherStmtFromStatements(m, \block(currentCase), currentEnv, volatileFields, currentAcquireActions, stmts);
	acquireActions += currentAcquireActions;
	fenv = mergeFlow(fenv, fenvInner);	
	exs = mergeExceptionState(exs, exsC);
	if(getBreakEnvironment(fenvInner) != ()){
		exitEnv = merge(exitEnv, getBreakEnvironment(fenvInner));
	}
	else{
		exitEnv = merge(exitEnv, currentEnv);
	}
	if(hasDefault){
		env = updateEnvironment(outerEnv, exitEnv);
	}
	else{
		env = mergeNestedEnvironment(outerEnv, exitEnv);
	}		
	return <stmts, env, flowEnvironment(getContinueEnvironment(fenv), (), getReturnEnvironment(fenv)), acquireActions, exs>;
}

//synchronizedStatement(Expression lock, Statement body)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc], AcquireActionsPaths, map[str, ExceptionState]] gatherStmtFromStatements(Declaration m, Statement s:synchronizedStatement(l, body), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, rel[loc,loc] actionsInPath, set[Stmt] stmts){
	<stmts, potential, env, actionsInPath, exs> = gatherStmtFromExpressions(m, exp, env, volatileFields, acquireActions, actionsInPath, stmts);
	stmts += potential;
	actionsInPath += extractAcquireActions(potential, volatileFields);
	
	loc vlock;
	for(w:read(_, name, _) <- potential){
		vlock = name;
	}
	
	<stmts, env, fenv, actionsInPath, actionsFromOtherPath, exsC> = gatherStmtFromStatements(m, body, env, volatileFields, acquireActions, {<s@src, vlock>} + actionsInPath, stmts);
	
	stmts += addAndUnlock(stmts, s@src, vlock);
	exs = mergeExceptionState(exs, exsC);
	return <stmts, env, fenv, actionsInPath, actionsFromOtherPath, exsC>;
}

//throw(Expression exp)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc], AcquireActionsPaths, map[str, ExceptionState]] gatherStmtFromStatements(Declaration m, Statement s:\throw(exp), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, rel[loc,loc] actionsInPath, set[Stmt] stmts){
	exs = (extractClassName(exp@decl) : exceptionState(env, acquireActions + actionsInPath));
	return <stmts, env, emptyFlowEnnvironment(), actionsInPath, emptyAcquireActionsPaths(), exs>;
}

//\try(Statement body, list[Statement] catchClauses)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc], AcquireActionsPaths, map[str, ExceptionState]] gatherStmtFromStatements(Declaration m, Statement s:\try(body, catchStatements), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, rel[loc,loc] actionsInPath, set[Stmt] stmts){
	<stmts, envTry, fenv, acquireActions, actionsFromOtherPaths, exsInner> = gatherStmtFromStatements(m, body, env, volatileFields, acquireActions, actionsInPath, stmts);
	env = updateEnvironment(env, envTry);	
	exitEnv = env;
	exs = ();
	
	for(cs <- catchStatements){
		<stmts, envC, fenvC, actionsInPathC, actionsFromOtherPathsC, exsC> = gatherStmtFromCatchStatements(m, cs, volatileFields, exsInner, stmts);	
		actionsInPath += acquireActionsC;
		exs = mergeExceptionState(exs,exsC);
		fenv = mergeFlow(fenv, fenvC);
		actionsFromOtherPaths = mergeExceptionState(actionsFromOtherPaths, actionsFromOtherPathsC);
		exitEnv = mergeNestedEnvironment(exitEnv, envC);
	}
	return <stmts, exitEnv, fenv, actionsInPath, actionsFromOtherPaths, exs>;
}

//\try(Statement body, list[Statement] catchClauses, Statement \finally)  
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc], AcquireActionsPaths, map[str, ExceptionState]] gatherStmtFromStatements(Declaration m, Statement s:\try(body, catchStatements, fin), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, rel[loc,loc] actionsInPath, set[Stmt] stmts){
	<stmts, envTry, fenv, acquireActions, actionsFromOtherPaths, exsInner> = gatherStmtFromStatements(m, body, env, volatileFields, acquireActions, actionsInPath, stmts);
	env = updateEnvironment(env, envTry);	
	exitEnv = env;
	exs = ();

	for(cs <- catchStatements){
		<stmts, envC, fenvC, actionsInPathC, actionsFromOtherPathsC, exsC> = gatherStmtFromCatchStatements(m, cs, volatileFields, exsInner, stmts);	
		actionsInPath += acquireActionsC;
		exs = mergeExceptionState(exs,exsC);
		fenv = mergeFlow(fenv, fenvC);
		actionsFromOtherPaths = mergeExceptionState(actionsFromOtherPaths, actionsFromOtherPathsC);
		exitEnv = mergeNestedEnvironment(exitEnv, envC);
	}
	//Run finally for every environemnt
	//exit
	<stmts, exitEnv, fenvE, actionsInPath, actionsFromOtherPaths,  exsE> = gatherStmtFromStatements(m, fin, exitEnv, volatileFields, acquireActions, actionsInPath, stmts);
	exs = mergeExceptionState(exs,exsE);
	//continue
	<stmts, envC, _, actionsInPathC, _, _> = gatherStmtFromStatements(m, fin, getContinueEnvironment(fenv), volatileFields, getAcquireActionsFromContinue(actionsFromOtherPaths), [], stmts);
	fenv = updateContinue(fenv, envC);
	actionsFromOtherPaths = addToActionsFromContinue(actionsFromOtherPaths, actionsInPathC);
	//break
	<stmts, envB, _, actionsInPathB, _, _> = gatherStmtFromStatements(m, fin, getBreakEnvironment(fenv), volatileFields, getAcquireActionsFromBreak(actionsFromOtherPaths), [], stmts);
	fenv = updateContinue(fenv, envB);
	actionsFromOtherPaths = addToActionsFromBreak(actionsFromOtherPaths, actionsInPathB);
	//return
	<stmts, envR, _, actionsInPathR, _, _> = gatherStmtFromStatements(m, fin, getReturnEnvironment(fenv), volatileFields, getAcquireActionsFromReturn(actionsFromOtherPaths), [], stmts);
	fenv = updateReturn(fenv, envR);
	actionsFromOtherPaths = addToActionsFromReturn(actionsFromOtherPaths, actionsInPathR);
	return <stmts, exitEnv, fenv, actionsInPath, actionsFromOtherPaths, exs>;
}

//\catch(Declaration exception, Statement body)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc], AcquireActionsPaths, map[str, ExceptionState]] gatherStmtFromCatchStatements(Declaration m, Statement s:\catch(except, body), set[loc] volatileFields, map[str, ExceptionState] exs, set[Stmt] stmts){
	env = ();
	fenv = emptyFlowEnvironment();
	map[str, ExceptionState] exsCatch = ();
	actionsFromOtherPaths = emptyAcquireActionsPaths();
	rel[loc,loc] actionsInPath = {};
	visit(except){
		case e:simpleName(_) : {
			<state, exs> = getAndRemoveExceptionState(e@decl.path, exs);
			if(!(state := emptyAcquireActionsPaths())){
				<stmts, envC, fenvCatch, actionsInPathCatch, actionsFromOtherPathsCatch, exsC> = gatherStmtFromStatements(m, body, getEnvironmentFromException(state), volatileFields, getAcquireActionsFromException(state), [], stmts);
				env = merge(env,envC);
				exsCatch = mergeExceptionState(exsCatch, exsC);
				fenv = mergeFlow(fenv, fenvCatch);
				actionsFromOtherPaths = mergeActions(actionsFromOtherPaths, actionsFromOtherPathsCatch);
				actionsInPath += actionsInPathCatch;
			}
			println("Unreached exception, <e@src>");
			//<stmts, envCatch, fenv, exsCatch> = gatherStmtFromStatements(m, updateEnvironment(env,envCatch), fenv, locks, stmts);
			//envCatch = merge(envCatch,env);
		}
	}
	return <stmts, env, fenv, actionsInPath, actionsFromOtherPaths, mergeExceptionState(exs, exsCatch)>;
}

//\declarationStatement(Declaration declaration)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc], AcquireActionsPaths, map[str, ExceptionState]] gatherStmtFromStatements(Declaration m, Statement s:\declarationStatement(d), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, rel[loc,loc] actionsInPath, set[Stmt] stmts){
	exs = ();
	fenv = emptyFlowEnvironment();
	actionsFromOtherPaths = emptyAcquireActionsPaths();
	top-down-break visit(d) {
		case Expression e : {
			<stmts, _, env, actionsInPath, exsE> = gatherStmtFromExpressions(m, e, env, volatileFields, acquireActions, actionsInPath, stmts);
			exs = mergeExceptionState(exs, exsE);
		}
		case Statement s : {
			<stmts, env, fenvD, actionsInPath, actionsFromOtherPathsD, exsD> = gatherStmtFromStatements(m, s, env, volatileFields, acquireActions, actionsInPath, stmts);
			exs = mergeExceptionState(exs, exsD);
			fenv = mergeFlow(fenv, fenvD);
			actionsFromOtherPaths = mergeExceptions(actionsFromOtherPaths, actionsFromOtherPathsD);
		}
	}
	return <stmts, env, fenv, actionsInPath, actionsFromOtherPaths, exs>;
}


//\while(Expression condition, Statement body)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc], AcquireActionsPaths, map[str, ExceptionState]] gatherStmtFromStatements(Declaration m, Statement s:\while(cond, body), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, rel[loc,loc] actionsInPath, set[Stmt] stmts){
	list[Expression] emptyList = [];
	return dealWithLoopsConditionFirst(m, emptyList, cond, emptyList, body, env, volatileFields, acquireActions, actionsInPath, stmts);
}

//\expressionStatement(Expression stmt)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc], AcquireActionsPaths, map[str, ExceptionState]] gatherStmtFromStatements(Declaration m, Statement s:expressionStatement(e), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, rel[loc,loc] actionsInPath, set[Stmt] stmts){
	<stmts, _, env, actionsInPath, exs> = gatherStmtFromExpressions(m, e, env, volatileFields, acquireActions, actionsInPath, stmts);
	return <stmts, env, emptyFlowEnvironment(), actionsInPath, emptyAcquireActionsPaths(), exs>;
}

 //\constructorCall(bool isSuper, Expression expr, list[Expression] arguments)
 tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc], AcquireActionsPaths, map[str, ExceptionState]] gatherStmtFromStatements(Declaration m, Statement s:constructorCall(isSuper, exp, args), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, rel[loc,loc] actionsInPath, set[Stmt] stmts){
 	exs = ();
	for(arg <- args){
		<stmts, potential, env, actionsInPath, exsC> = gatherStmtFromExpressions(m, arg, env, volatileFields, acquireActions, actionsInPath, stmts);
		stmts += potential;
		actionsInPath += extractAcquireActions(potential, volatileFields);
		exs = mergeExceptionState(exs,exsC);
	}
	<stmts, potential, env, actionsInPath, exsC> = gatherStmtFromExpressions(m, exp, env, volatileFields, acquireActions, actionsInPath, stmts);
	stmts += potential;
	actionsInPath += extractAcquireActions(potential, volatileFields);
	exs = mergeExceptionState(exs,exsC);
		
	return <stmts, env, emptyFlowEnvironment(), actionsInPath, emptyAcquireActionsPaths(), exs>;
}
 //\constructorCall(bool isSuper, list[Expression] arguments)
 tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc], map[str, ExceptionState]] gatherStmtFromStatements(Declaration m, Statement s:constructorCall(isSuper, args), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, rel[loc,loc] actionsInPath, set[Stmt] stmts){
	 return gatherStmtFromStatements(m, constructorCall(isSuper, Expression::null(), args), env, volatileFields, acquireActions, actionsInPath, stmts);
 }

tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc], map[str, ExceptionState]] gatherStmtFromStatements(Declaration m, Statement b:empty(), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, rel[loc,loc] actionsInPath, set[Stmt] stmts){
	return <stmts, env, emptyFlowEnvironment(), actionsInPath, emptyAcquireActionsPaths(), exs>;
}

default tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc], map[str, ExceptionState]] gatherStmtFromStatements(Declaration m, Statement b, map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, rel[loc,loc] actionsInPath, set[Stmt] stmts){
	println("case I do not need : <b>");
	return <stmts, env, emptyFlowEnvironment(), actionsInPath, emptyAcquireActionsPaths(), ()>;
}

