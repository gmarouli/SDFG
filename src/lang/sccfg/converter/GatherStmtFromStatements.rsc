module lang::sccfg::converter::GatherStmtFromStatements

import IO;

import lang::java::jdt::m3::AST;

import lang::sccfg::ast::DataFlowLanguage;
import lang::sccfg::converter::GatherStmtFromExpressions;

import lang::sccfg::converter::util::State;
import lang::sccfg::converter::util::Getters;
import lang::sccfg::converter::util::ExceptionManagement;
import lang::sccfg::converter::util::EnvironmentManagement;
import lang::sccfg::converter::util::AcquireActionsManagement;
import lang::sccfg::converter::util::TypeSensitiveEnvironment;

////assert(Expression expression)
//tuple[set[Stmt], map[loc,set[loc]], FlowEnvironment, rel[loc,loc], AcquireActionsPaths, map[str, State]] gatherStmtFromStatements(Declaration m, Statement s:\assert(exp), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, rel[loc,loc] actionsInPath, set[Stmt] stmts){
//	return gatherStmtFromStatements(m, \assert(exp, Expression::null()), env, volatileFields, actionsInPath, stmts);
//}
//
////assert(Expression expression, Expression message)
//tuple[set[Stmt], map[loc,set[loc]], FlowEnvironment, rel[loc,loc], AcquireActionsPaths, map[str, State]] gatherStmtFromStatements(Declaration m, Statement s:\assert(exp, message), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, rel[loc,loc] actionsInPath, set[Stmt] stmts){
//	<stmts, potential, env, exs> = gatherStmtFromExpressions(m, exp, env, volatileFields, acquireActions, actionsInPath, stmts);
//	stmts += potential;
//	actionsInPath += extractAcquireAction(potential, volatileFields);
//	
//	<stmts, potential, envM, exsM> = gatherStmtFromExpressions(m, message, env, volatileFields, acquireActions, actionsInPath, stmts);
//	stmts += potential;
//	actionsInExitPath += extractAcquireAction(potential, volatileFields);
//	exs = mergeState(exs, exsM);
//	//the volatile access from the message are not counted since if the message appears nothing else is going to be executed
//	//The assert is a possible an exit point, in case of finally we can see it as a return
//	env = mergeNestedEnvironment(env,envM);
//	return <stmts, env, initializeReturnEnvironment(env), actionsInPath, initializeAcquireActionsFromReturn(actionsInExitPath), exs>;
//}
//
//block(list[Statement] statements)
tuple[set[Stmt], map[loc, set[loc]], map[loc, TypeSensitiveEnvironment], rel[loc,loc], FlowEnvironment, map[str, State]] gatherStmtFromStatements(Statement s:\block(sB), map[loc, set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	exs = ();
	fenv = emptyFlowEnvironment();
	for(stmt <- sB){
		<stmts, env, typesOf, acquireActions, fenvS, exsS> = gatherStmtFromStatements(stmt, env, typesOf, volatileFields, acquireActions, stmts);
		fenv = mergeFlow(fenv, fenvS);
		exs = mergeExceptions(exs, exsS);
		if(breakingControlFlow(stmt))
			break;
	}
	return <stmts, env, typesOf, acquireActions, fenv, exs>;
}

//break()
tuple[set[Stmt], map[loc, set[loc]], map[loc, TypeSensitiveEnvironment], rel[loc,loc], FlowEnvironment, map[str, State]] gatherStmtFromStatements(Statement s:\break(), map[loc, set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts)
	= <stmts, (), (), {}, initializeBreakState(env, typesOf, acquireActions), ()>;

//break("")
tuple[set[Stmt], map[loc, set[loc]], map[loc, TypeSensitiveEnvironment], rel[loc,loc], FlowEnvironment, map[str, State]] gatherStmtFromStatements(Statement s:\break(""), map[loc, set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts)
	= <stmts, (), (), {}, initializeBreakState(env, typesOf, acquireActions), ()>;

//break(str label)
tuple[set[Stmt], map[loc, set[loc]], map[loc, TypeSensitiveEnvironment], rel[loc,loc], FlowEnvironment, map[str, State]] gatherStmtFromStatements(Statement s:\break(exp), map[loc, set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	if(exp == "")
		fail;
	assert false : "Labeled statement (break) found!!!";
	return <stmts, (), (), {}, initializeBreakState(env, typesOf, acquireActions), ()>;
}

//continue()
tuple[set[Stmt], map[loc, set[loc]], map[loc, TypeSensitiveEnvironment], rel[loc,loc], FlowEnvironment, map[str, State]] gatherStmtFromStatements(Statement s:\continue(), map[loc, set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts)
	= <stmts, (), (), {}, initializeContinueState(env, typesOf, acquireActions), ()>;

//continue(str label)
tuple[set[Stmt], map[loc, set[loc]], map[loc, TypeSensitiveEnvironment], rel[loc,loc], FlowEnvironment, map[str, State]] gatherStmtFromStatements(Statement s:\continue(_), map[loc, set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	assert false : "Labeled statement (continue) found!!!";
	return <stmts, (), (), {}, initializeContinueState(env, typesOf, acquireActions), ()>;
}

////do(Statement body, Expression condition)
//tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc], AcquireActionsPaths, map[str, State]] gatherStmtFromStatements(Declaration m, Statement s:\do(b, cond), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, rel[loc,loc] actionsInPath, set[Stmt] stmts){
//		
//	//executed once all the reads and assigns added missing connections to itself
//	<stmts, env, fenvInner, acquireActions, exs> = gatherStmtFromStatements(m, b, env, volatileFields, acquireActions, stmts);
//			
//	//include continue
//	env = mergeNestedEnvironment(env, getContinueEnvironment(fenvInner));
//			
//	//running the condition after one loop getting all the connections from statements and continue command
//	<stmts, potential, env, acquireActions, exsC> = gatherStmtFromExpressions(m, cond, env, volatileFields, acquireActions, stmts);
//	exs = mergeState(exs, exsC);
//	stmts += potential;
//	acquireActions += extractAcquireActions(potential, volatileFields);
//	
//	//connect the statements with the condition but the environment and exception are already found
//	<stmts, env, _, exsC> = gatherStmtFromStatements(m, b, env, volatileFields, acquireActions, stmts);
//
//	env = mergeNestedEnvironment(env, getBreakEnvironment(fenvInner));
//	
//	return <stmts, env, initializeReturnEnvironment(getReturnEnvironment(fenvInner)), acquireActions, exs>;
//}
//
////foreach(Declaration parameter, Expression collection, Statement body)
//tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc], AcquireActionsPaths, map[str, State]] gatherStmtFromStatements(Declaration m, Statement s:\foreach(parameter, collection, body), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, rel[loc,loc] actionsInPath, set[Stmt] stmts){
//	outerEnv = env;
//	<stmts, potential, env, exs> = gatherStmtFromExpressions(m, collection, env, volatileFields, acquireActions, stmts);
//	stmts += potential;
//	acquireActions += extractAcquireActions(potential, volatileFields);
//	//this variable is declared locally it cannot be volatile
//	stmt += addAndLock({Stmt::assign(s@src, parameter@decl, s@src)}, acquireActions);
//	env[parameter@decl] = {s@src};
//	
//	outerEnv = updateEnvironment(outerEnv, env);
//	
//	//executed once all the reads and assigns added missing connections to itself
//	<stmts, env, fenvInner, exsC> = gatherStmtFromStatements(m, b, env, volatileFields, acquireActions, stmts);
//	exs = mergeState(exs,exsC);		
//	//include continue
//	env = mergeNestedEnvironment(env, getContinueEnvironment(fenvInner));
//			
//	//running the condition after one loop getting all the connections from statements and continue command
//	<stmts, potential, env, _> = gatherStmtFromExpressions(m, collection, env, volatileFields, acquireActions, stmts);
//	stmts += potential;
//	
//	//connect the statements with the condition but the environment and exception are already found
//	<stmts, env, _, _> = gatherStmtFromStatements(m, b, env, volatileFields, acquireActions, stmts);
//
//	env = mergeNestedEnvironment(env, getBreakEnvironment(fenvInner));
//	
//	return <stmts, mergeNestedEnvironment(outerEnv,env), emptyFlowEnvironment(), acquireActions, exs>;
//}
//
////for(list[Expression] initializers, Expression condition, list[Expression] updaters, Statement body)
//tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc], AcquireActionsPaths, map[str, State]] gatherStmtFromStatements(Declaration m, Statement s:\for(initializers, cond, updaters, body), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, rel[loc,loc] actionsInPath, set[Stmt] stmts){
//	return dealWithLoopsConditionFirst(m, initializers, cond, updaters, body, env, volatileFields, acquireActions, stmts);
//} 
//
////for(list[Expression] initializers, list[Expression] updaters, Statement body)
//tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc], AcquireActionsPaths, map[str, State]] gatherStmtFromStatements(Declaration m, Statement s:\for(initializers, updaters, body), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, rel[loc,loc] actionsInPath, set[Stmt] stmts){
//	return dealWithLoopsConditionFirst(m, initializers, Expression::\null(), updaters, body, env, volatileFields, acquireActions, stmts);
//}
//
//expressionStatement(Expression stmt)
tuple[set[Stmt], map[loc, set[loc]], map[loc, TypeSensitiveEnvironment], rel[loc,loc], FlowEnvironment, map[str, State]] gatherStmtFromStatements(Statement s:\expressionStatement(e), map[loc, set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	<stmts, _, env, typesOf, acquireActions, exs> = gatherStmtFromExpressions(e, env, typesOf, volatileFields, acquireActions, stmts);
	return <stmts, env, typesOf, acquireActions, emptyFlowEnvironment(), exs>;
}

//if(Expression condition, Statement thenB)
tuple[set[Stmt], map[loc, set[loc]], map[loc, TypeSensitiveEnvironment], rel[loc,loc], FlowEnvironment, map[str, State]] gatherStmtFromStatements(Statement s:\if(cond, thenB), map[loc, set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	<stmts, potential, env, typesOf, acquireActions, exs> = gatherStmtFromExpressions(cond, env, typesOf, volatileFields, acquireActions, stmts);
	stmts += potential;
	acquireActions += extractAcquireActions(potential, volatileFields);
	
	<stmts, envOpt, typesOpt, acquireActionsThen, fenv, exsC> = gatherStmtFromStatements(thenB, env, typesOf, volatileFields, acquireActions, stmts);
	exs = mergeExceptions(exs,exsC);
	env = mergeNestedEnvironment(env,envOpt);
	typesOf = mergeTypesEnvironment(typesOf, typesOpt);
	
	return <stmts, env, typesOf, acquireActions + acquireActionsThen, fenv, exs>;
}

//if(Expression condition, Statement thenB, Statement elseB)
tuple[set[Stmt], map[loc, set[loc]], map[loc, TypeSensitiveEnvironment], rel[loc,loc], FlowEnvironment, map[str, State]] gatherStmtFromStatements(Statement s:\if(cond, thenB, elseB), map[loc, set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	<stmts, potential, env, typesOf, acquireActions, exs> = gatherStmtFromExpressions(cond, env, typesOf, volatileFields, acquireActions, stmts);
	stmts += potential;
	acquireActions += extractAcquireActions(potential, volatileFields);
	
	<stmtsIf,   envIf,   typesIf,   acquireActionsIf,   fenvIf,   exsIf> = gatherStmtFromStatements(thenB, env, typesOf, volatileFields, acquireActions, stmts);
	<stmtsElse, envElse, typesElse, acquireActionsElse, fenvElse, exsElse> = gatherStmtFromStatements(elseB, env, typesOf, volatileFields, acquireActions, stmts);
	
	env = mergeNestedEnvironment(envIf,envElse);
	typesOf = mergeTypeEnvironment(typesIf, typesElse);
	fenv = mergeFlow(fenvIf, fenvElse);
	exs = mergeExceptions(exsIf,exsElse);
	return <stmtsIf + stmtsElse, env, typesOf, acquireActionsIf + acquireActionsElse, fenv, exs>;
}

//label(str name, Statement body)
tuple[set[Stmt], map[loc, set[loc]], map[loc, TypeSensitiveEnvironment], rel[loc,loc], FlowEnvironment, map[str, State]] gatherStmtFromStatements(Statement s:\label(_, _), map[loc, set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	assert false: "Labeled block";
	return <stmts, env, typesOf, acquireActions, emptyFlowEnvironment(), ()>;
}

//return(Expression expression)
tuple[set[Stmt], map[loc, set[loc]], map[loc, TypeSensitiveEnvironment], rel[loc,loc], FlowEnvironment, map[str, State]] gatherStmtFromStatements(Statement s:\return(exp), map[loc, set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	<stmts, potential, env, typesOf, acquireActions, exs> = gatherStmtFromExpressions(exp, env, typesOf, volatileFields, acquireActions, stmts);
	stmts += potential;
	acquireActions += extractAcquireActions(potential, volatileFields); //needed for the finally
	return <stmts, (), (), {}, initializeReturnState(env, typesOf, acquireActions), exs>;
}

//return()
tuple[set[Stmt], map[loc, set[loc]], map[loc, TypeSensitiveEnvironment], rel[loc,loc], FlowEnvironment, map[str, State]] gatherStmtFromStatements(Statement s:\return(), map[loc, set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts)
	= <stmts, (), (), {}, initializeReturnState(env, typesOf, acquireActions), exs>;

////switch(Expression exp, list[Statement] statements)
//tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc], AcquireActionsPaths, map[str, State]] gatherStmtFromStatements(Declaration m, Statement s:\switch(exp, body), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, rel[loc,loc] actionsInPath, set[Stmt] stmts){
//	<stmts, potential, env, actionsInPath, exs> = gatherStmtFromExpressions(m, exp, env, volatileFields, acquireActions, actionsInPath, stmts);
//	stmts += potential;
//	actionsInPath += extractAcquireActions(potential, volatileFields);
//	
//	outerEnv = env;
//	rel[loc,loc] outerAcquireActions = acquireActions + actionsInPath;
//	rel[loc,loc] currentAcquireActions = acquireActions + actionsInPath;
//	exitEnv = ();
//	fenv = emptyFlowEnvironment();
//	
//	list[Statement] currentCase = [];
//	hasDefault = false;
//	for(stmt <- body){
//		switch(stmt){
//			case \case(_):{
//				<stmts, currentEnv, fenvInner, currentAcquireActions, exsC> = gatherStmtFromStatements(m, \block(currentCase), currentEnv, volatileFields, currentAcquireActions, stmts);
//				acquireActions += currentAcquireActions;
//				exs = mergeState(exs, exsC);
//				fenv = mergeFlow(fenv, fenvInner);
//				currentCase = [];
//						
//				if(getBreakEnvironment(fenvInner) != ()){
//					exitEnv = merge(exitEnv, getBreakEnvironment(fenvInner));
//					currentEnv = outerEnv;
//					currentAcquireActions = outerAcquireActions;
//				}
//				else{
//					currentEnv = updateEnvironment(outerEnv, currentEnv);
//				}
//			}
//			case  \defaultCase():{
//				hasDefault = true;
//				<stmts, currentEnv, fenvInner, currentAcquireActions, exsC> = gatherStmtFromStatements(m, \block(currentCase), currentEnv, volatileFields, currentAcquireActions, stmts);
//				acquireActions += currentAcquireActions;
//				exs = mergeState(exs, exsC);
//				fenv = mergeFlow(fenv, fenvInner);
//				currentCase = [];
//							
//				if(getBreakEnvironment(fenvInner) != ()){
//					exitEnv = merge(exitEnv, getBreakEnvironment(fenvInner));
//					currentEnv = outerEnv;
//					currentAcquireActions = outerAcquireActions;
//				}
//				else{
//					currentEnv = updateEnvironment(outerEnv, currentEnv);
//				}
//			}
//			default:{
//				currentCase += [stmt];
//			}
//		}
//	}
//
//	<stmts, currentEnv, fenvInner, currentAcquireActions, exsC> = gatherStmtFromStatements(m, \block(currentCase), currentEnv, volatileFields, currentAcquireActions, stmts);
//	acquireActions += currentAcquireActions;
//	fenv = mergeFlow(fenv, fenvInner);	
//	exs = mergeState(exs, exsC);
//	if(getBreakEnvironment(fenvInner) != ()){
//		exitEnv = merge(exitEnv, getBreakEnvironment(fenvInner));
//	}
//	else{
//		exitEnv = merge(exitEnv, currentEnv);
//	}
//	if(hasDefault){
//		env = updateEnvironment(outerEnv, exitEnv);
//	}
//	else{
//		env = mergeNestedEnvironment(outerEnv, exitEnv);
//	}		
//	return <stmts, env, flowEnvironment(getContinueEnvironment(fenv), (), getReturnEnvironment(fenv)), acquireActions, exs>;
//}
//
////synchronizedStatement(Expression lock, Statement body)
//tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc], AcquireActionsPaths, map[str, State]] gatherStmtFromStatements(Declaration m, Statement s:synchronizedStatement(l, body), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, rel[loc,loc] actionsInPath, set[Stmt] stmts){
//	<stmts, potential, env, actionsInPath, exs> = gatherStmtFromExpressions(m, exp, env, volatileFields, acquireActions, actionsInPath, stmts);
//	stmts += potential;
//	actionsInPath += extractAcquireActions(potential, volatileFields);
//	
//	loc vlock;
//	for(w:read(_, name, _) <- potential){
//		vlock = name;
//	}
//	
//	<stmts, env, fenv, actionsInPath, actionsFromOtherPath, exsC> = gatherStmtFromStatements(m, body, env, volatileFields, acquireActions, {<s@src, vlock>} + actionsInPath, stmts);
//	
//	stmts += addAndUnlock(stmts, s@src, vlock);
//	exs = mergeState(exs, exsC);
//	return <stmts, env, fenv, actionsInPath, actionsFromOtherPath, exsC>;
//}
//
////throw(Expression exp)
//tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc], AcquireActionsPaths, map[str, State]] gatherStmtFromStatements(Declaration m, Statement s:\throw(exp), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, rel[loc,loc] actionsInPath, set[Stmt] stmts){
//	exs = (extractClassName(exp@decl) : exceptionState(env, acquireActions + actionsInPath));
//	return <stmts, env, emptyFlowEnnvironment(), actionsInPath, emptyAcquireActionsPaths(), exs>;
//}
//
////\try(Statement body, list[Statement] catchClauses)
//tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc], AcquireActionsPaths, map[str, State]] gatherStmtFromStatements(Declaration m, Statement s:\try(body, catchStatements), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, rel[loc,loc] actionsInPath, set[Stmt] stmts){
//	<stmts, envTry, fenv, acquireActions, actionsFromOtherPaths, exsInner> = gatherStmtFromStatements(m, body, env, volatileFields, acquireActions, actionsInPath, stmts);
//	env = updateEnvironment(env, envTry);	
//	exitEnv = env;
//	exs = ();
//	
//	for(cs <- catchStatements){
//		<stmts, envC, fenvC, actionsInPathC, actionsFromOtherPathsC, exsC> = gatherStmtFromCatchStatements(m, cs, volatileFields, exsInner, stmts);	
//		actionsInPath += acquireActionsC;
//		exs = mergeState(exs,exsC);
//		fenv = mergeFlow(fenv, fenvC);
//		actionsFromOtherPaths = mergeState(actionsFromOtherPaths, actionsFromOtherPathsC);
//		exitEnv = mergeNestedEnvironment(exitEnv, envC);
//	}
//	return <stmts, exitEnv, fenv, actionsInPath, actionsFromOtherPaths, exs>;
//}
//
////\try(Statement body, list[Statement] catchClauses, Statement \finally)  
//tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc], AcquireActionsPaths, map[str, State]] gatherStmtFromStatements(Declaration m, Statement s:\try(body, catchStatements, fin), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, rel[loc,loc] actionsInPath, set[Stmt] stmts){
//	<stmts, envTry, fenv, acquireActions, actionsFromOtherPaths, exsInner> = gatherStmtFromStatements(m, body, env, volatileFields, acquireActions, actionsInPath, stmts);
//	env = updateEnvironment(env, envTry);	
//	exitEnv = env;
//	exs = ();
//
//	for(cs <- catchStatements){
//		<stmts, envC, fenvC, actionsInPathC, actionsFromOtherPathsC, exsC> = gatherStmtFromCatchStatements(m, cs, volatileFields, exsInner, stmts);	
//		actionsInPath += acquireActionsC;
//		exs = mergeState(exs,exsC);
//		fenv = mergeFlow(fenv, fenvC);
//		actionsFromOtherPaths = mergeState(actionsFromOtherPaths, actionsFromOtherPathsC);
//		exitEnv = mergeNestedEnvironment(exitEnv, envC);
//	}
//	//Run finally for every environemnt
//	//exit
//	<stmts, exitEnv, fenvE, actionsInPath, actionsFromOtherPaths,  exsE> = gatherStmtFromStatements(m, fin, exitEnv, volatileFields, acquireActions, actionsInPath, stmts);
//	exs = mergeState(exs,exsE);
//	//continue
//	<stmts, envC, _, actionsInPathC, _, _> = gatherStmtFromStatements(m, fin, getContinueEnvironment(fenv), volatileFields, getAcquireActionsFromContinue(actionsFromOtherPaths), [], stmts);
//	fenv = updateContinue(fenv, envC);
//	actionsFromOtherPaths = addToActionsFromContinue(actionsFromOtherPaths, actionsInPathC);
//	//break
//	<stmts, envB, _, actionsInPathB, _, _> = gatherStmtFromStatements(m, fin, getBreakEnvironment(fenv), volatileFields, getAcquireActionsFromBreak(actionsFromOtherPaths), [], stmts);
//	fenv = updateContinue(fenv, envB);
//	actionsFromOtherPaths = addToActionsFromBreak(actionsFromOtherPaths, actionsInPathB);
//	//return
//	<stmts, envR, _, actionsInPathR, _, _> = gatherStmtFromStatements(m, fin, getReturnEnvironment(fenv), volatileFields, getAcquireActionsFromReturn(actionsFromOtherPaths), [], stmts);
//	fenv = updateReturn(fenv, envR);
//	actionsFromOtherPaths = addToActionsFromReturn(actionsFromOtherPaths, actionsInPathR);
//	return <stmts, exitEnv, fenv, actionsInPath, actionsFromOtherPaths, exs>;
//}
//
////\catch(Declaration exception, Statement body)
//tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc], AcquireActionsPaths, map[str, State]] gatherStmtFromCatchStatements(Declaration m, Statement s:\catch(except, body), set[loc] volatileFields, map[str, State] exs, set[Stmt] stmts){
//	env = ();
//	fenv = emptyFlowEnvironment();
//	map[str, State] exsCatch = ();
//	actionsFromOtherPaths = emptyAcquireActionsPaths();
//	rel[loc,loc] actionsInPath = {};
//	visit(except){
//		case e:simpleName(_) : {
//			<state, exs> = getAndRemoveState(e@decl.path, exs);
//			if(!(state := emptyAcquireActionsPaths())){
//				<stmts, envC, fenvCatch, actionsInPathCatch, actionsFromOtherPathsCatch, exsC> = gatherStmtFromStatements(m, body, getEnvironmentFromException(state), volatileFields, getAcquireActionsFromException(state), [], stmts);
//				env = merge(env,envC);
//				exsCatch = mergeState(exsCatch, exsC);
//				fenv = mergeFlow(fenv, fenvCatch);
//				actionsFromOtherPaths = mergeActions(actionsFromOtherPaths, actionsFromOtherPathsCatch);
//				actionsInPath += actionsInPathCatch;
//			}
//			println("Unreached exception, <e@src>");
//			//<stmts, envCatch, fenv, exsCatch> = gatherStmtFromStatements(m, updateEnvironment(env,envCatch), fenv, locks, stmts);
//			//envCatch = merge(envCatch,env);
//		}
//	}
//	return <stmts, env, fenv, actionsInPath, actionsFromOtherPaths, mergeState(exs, exsCatch)>;
//}
//
//\declarationStatement(Declaration declaration)
tuple[set[Stmt], map[loc, set[loc]], map[loc, TypeSensitiveEnvironment], rel[loc,loc], FlowEnvironment, map[str, State]] gatherStmtFromStatements(Statement ds:\declarationStatement(d), map[loc, set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	exs = ();
	fenv = emptyFlowEnvironment();
	top-down-break visit(d) {
		case Expression e : {
			<stmts, _, env, typesOf, acquireActions, exsE> = gatherStmtFromExpressions(e, env, typesOf, volatileFields, acquireActions, stmts);
			exs = mergeExceptions(exs, exsE);
		}
		case Statement s : {
			<stmts, env, typesOf, acquireActions, fenvD, exsD> = gatherStmtFromStatements(s, env, typesOf, volatileFields, acquireActions, stmts);
			exs = mergeExceptions(exs, exsD);
			fenv = mergeFlow(fenv, fenvD);
		}
	}
	return <stmts, env, typesOf, acquireActions, fenv, exs>;
}

////\while(Expression condition, Statement body)
//tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc], AcquireActionsPaths, map[str, State]] gatherStmtFromStatements(Declaration m, Statement s:\while(cond, body), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, rel[loc,loc] actionsInPath, set[Stmt] stmts){
//	list[Expression] emptyList = [];
//	return dealWithLoopsConditionFirst(m, emptyList, cond, emptyList, body, env, volatileFields, acquireActions, actionsInPath, stmts);
//}
//
tuple[set[Stmt], map[loc, set[loc]], map[loc, TypeSensitiveEnvironment], rel[loc,loc], FlowEnvironment, map[str, State]] gatherStmtFromStatements(Statement s:\while(cond, body), map[loc, set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	<stmts, potential, env, typesOf, acquireActions, exs> = gatherStmtFromExpressions(cond, env, typesOf, volatileFields, acquireActions, stmts);
	stmts += potential;
	acquireActions += extractAcquireActions(potential, volatileFields);
	exitEnv = env;
	exitTypesOf = typesOf;
	exitAcquireActions = acquireActions;
	exitExs = exs;
	
	<stmts, envB, typesOfB, acquireActionsB, fenvB, exsB> = gatherStmtFromStatements(body, env, typesOf, volatileFields, acquireActions, stmts);
	exitEnv = mergeNestedEnvironment(exitEnv, getEnvironment(getBreakState(fenvB)));
	exitTypesOf = mergeTypesEnvironment(exitTypesOf, getTypesEnvironment(getBreakState(fenvB)));
	exitAcquireActions += getAcquireActions(getBreakState(fenvB));
	exitExs = mergeExceptions(exitExs, exsB);
	
	envB = updateEnvironment(env, envB);
	envB = mergeNestedEnvironment(envB, getEnvironment(getContinueState(fenvB)));
	typesOfB = mergeTypesEnvironment(exitTypesOf, getTypesEnvironment(getContinueState(fenvB)));
	acquireActionsB += getAcquireActions(getContinueState(fenvB));
	
	<stmts, potential, env, typesOf, acquireActions, exs> = gatherStmtFromExpressions(cond, envB, typesOfB, volatileFields, acquireActionsB, stmts);
	stmts += potential;
	exitExs = mergeExceptions(exitExs, exs);
	
	exitEnv = mergeNestedEnvironment(exitEnv, env);
	exitTypesOf = mergeTypesEnvironment(exitTypesOf, typesOf);
	exitAcquireActions += getAcquireActions(getBreakState(fenvB));
	
	<stmts, _, _, _, fenvB, exs> = gatherStmtFromStatements(body, env, typesOf, volatileFields, acquireActions, stmts);
	exitEnv = mergeNestedEnvironment(exitEnv, getEnvironment(getBreakState(fenvB)));
	exitTypesOf = mergeTypesEnvironment(exitTypesOf, getTypesEnvironment(getBreakState(fenvB)));
	exitAcquireActions += getAcquireActions(getBreakState(fenvB));
	exitExs = mergeExceptions(exitExs, exsB);
	
	return <stmts, exitEnv, exitTypesOf,  acquireActions, initializeReturnState(getReturnState(fenvB)), exs>;
}

//\expressionStatement(Expression stmt)
tuple[set[Stmt], map[loc, set[loc]], map[loc, TypeSensitiveEnvironment], rel[loc,loc], FlowEnvironment, map[str, State]] gatherStmtFromStatements(Statement s:expressionStatement(e), map[loc, set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	<stmts, _, env, typesOf, acquireActions, exs> = gatherStmtFromExpressions(e, env, typesOf, volatileFields, acquireActions, stmts);
	return <stmts, env, typesOf, acquireActions, emptyFlowEnvironment(), exs>;
}

// //\constructorCall(bool isSuper, Expression expr, list[Expression] arguments)
// tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc], AcquireActionsPaths, map[str, State]] gatherStmtFromStatements(Declaration m, Statement s:constructorCall(isSuper, exp, args), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, rel[loc,loc] actionsInPath, set[Stmt] stmts){
// 	exs = ();
//	for(arg <- args){
//		<stmts, potential, env, actionsInPath, exsC> = gatherStmtFromExpressions(m, arg, env, volatileFields, acquireActions, actionsInPath, stmts);
//		stmts += potential;
//		actionsInPath += extractAcquireActions(potential, volatileFields);
//		exs = mergeState(exs,exsC);
//	}
//	<stmts, potential, env, actionsInPath, exsC> = gatherStmtFromExpressions(m, exp, env, volatileFields, acquireActions, actionsInPath, stmts);
//	stmts += potential;
//	actionsInPath += extractAcquireActions(potential, volatileFields);
//	exs = mergeState(exs,exsC);
//		
//	return <stmts, env, emptyFlowEnvironment(), actionsInPath, emptyAcquireActionsPaths(), exs>;
//}
// //\constructorCall(bool isSuper, list[Expression] arguments)
// tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc], map[str, State]] gatherStmtFromStatements(Declaration m, Statement s:constructorCall(isSuper, args), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, rel[loc,loc] actionsInPath, set[Stmt] stmts){
//	 return gatherStmtFromStatements(m, constructorCall(isSuper, Expression::null(), args), env, volatileFields, acquireActions, actionsInPath, stmts);
// }
//
//tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc], map[str, State]] gatherStmtFromStatements(Declaration m, Statement b:empty(), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, rel[loc,loc] actionsInPath, set[Stmt] stmts){
//	return <stmts, env, emptyFlowEnvironment(), actionsInPath, emptyAcquireActionsPaths(), exs>;
//}
//
default tuple[set[Stmt], map[loc, set[loc]], map[loc, TypeSensitiveEnvironment], rel[loc,loc], FlowEnvironment, map[str, State]] gatherStmtFromStatements(Statement b, map[loc, set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	println("case I do not need : <b>");
	return <stmts, env, typesOf, acquireActions, emptyFlowEnvironment(), ()>;
}

bool breakingControlFlow(Statement s:\continue()) = true;
bool breakingControlFlow(Statement s:\break()) = true;
bool breakingControlFlow(Statement s:\break("")) = true;
bool breakingControlFlow(Statement s:\return()) = true;
bool breakingControlFlow(Statement s:\return(_)) = true;
default bool breakingControlFlow(Statement s) =  false;

