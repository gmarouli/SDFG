module lang::sccfg::converter::GatherStmtFromStatements

import IO;

import lang::java::jdt::m3::AST;

import lang::sccfg::ast::DataFlowLanguage;
import lang::sccfg::converter::GatherStmtFromExpressions;

import lang::sccfg::converter::util::State;
import lang::sccfg::converter::util::Getters;
import lang::sccfg::converter::util::ExceptionManagement;
import lang::sccfg::converter::util::EnvironmentManagement;
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

//do(Statement body, Expression condition)
tuple[set[Stmt], map[loc, set[loc]], map[loc, TypeSensitiveEnvironment], rel[loc,loc], FlowEnvironment, map[str, State]] gatherStmtFromStatements(Statement s:\do(b, cond), map[loc, set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
		
	//executed once all the reads and assigns added missing connections to itself
	<stmts, env, typesOf, acquireActions, fenv, exitExs> = gatherStmtFromStatements(b, env, typesOf, volatileFields, acquireActions, stmts);
	env = merge(env, getEnvironment(getContinueState(fenv)));
	typesOf = mergeTypesEnvironment(typesOf, getTypesEnvironment(getContinueState(fenv)));
	acquireActions += getAcquireActions(getContinueState(fenv));
	
	exitEnv = getEnvironment(getBreakState(fenv));
	exitTypesOf = getTypesEnvironment(getBreakState(fenv));
	exitAcquireActions = getAcquireActions(getBreakState(fenv));
	
	<stmts, potential, env, typesOf, acquireActions, exs> = gatherStmtFromExpressions(cond, env, typesOf, volatileFields, acquireActions, stmts);
	stmts += potential;
	acquireActions += extractAcquireActions(potential, volatileFields);
	exitExs = mergeExceptions(exitExs, exs);
	exitEnv = merge(exitEnv, env);
	exitTypesOf = mergeTypesEnvironment(exitTypesOf, typesOf);
	exitAcquireActions += acquireActions;
	
	<stmts, _, _, _, fenvB, exs> = gatherStmtFromStatements(b, env, typesOf, volatileFields, acquireActions, stmts);
	exitEnv = merge(exitEnv, getEnvironment(getBreakState(fenvB)));
	exitTypesOf = mergeTypesEnvironment(exitTypesOf, getTypesEnvironment(getBreakState(fenvB)));
	exitAcquireActions += getAcquireActions(getBreakState(fenvB));
	exitExs = mergeExceptions(exitExs, exs);
	fenv = mergeFlow(fenv, fenvB);
	
	return <stmts, exitEnv, exitTypesOf,  exitAcquireActions, initializeReturnState(getReturnState(fenv)), exs>;
}
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
	
	println(envIf);
	println(envElse);
	env = mergeNestedEnvironment(envIf,envElse);
	typesOf = mergeTypesEnvironment(typesIf, typesElse);
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

//switch(Expression exp, list[Statement] statements)
tuple[set[Stmt], map[loc, set[loc]], map[loc, TypeSensitiveEnvironment], rel[loc,loc], FlowEnvironment, map[str, State]] gatherStmtFromStatements(Statement s:\switch(exp, body), map[loc, set[loc]] env, map[loc,TypeSensitiveEnvironment] typesOf, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	<stmts, potential, env, typesOf, acquireActions, exs> = gatherStmtFromExpressions(exp, env, typesOf, volatileFields, acquireActions, stmts);
	stmts += potential;
	acquireActions += extractAcquireActions(potential, volatileFields);
	
	exitStmts = stmts;
	exitEnv = ();
	exitTypesOf = ();
	exitAcquireActions = acquireActions;
	exitFenv = emptyFlowEnvironment();
	
	currentStmts = stmts;
	currentEnv = env;
	currentTypesOf = typesOf;
	currentAcquireActions = acquireActions;
	
	list[Statement] currentCase = [];

	hasDefault = false;
	for(stmt <- body){
		switch(stmt){
			case \case(_):{
				<currentStmts, currentEnv, currentTypeOf, currentAcquireActions, fenv, exsC> = gatherStmtFromStatements(\block(currentCase), currentEnv, currentTypesOf, volatileFields, currentAcquireActions, currentStmts);
				if(isEmpty(getBreakState(fenv))){
					currentEnv = merge(env, currentEnv);
					currentTypesOf = mergeTypesEnvironment(typesOf, currentTypesOf);
				}
				else{
					exitStmts += currentStmts;
					exitEnv = merge(exitEnv, getEnvironment(getBreakState(fenv)));
					exitTypesOf = mergeTypesEnvironment(exitTypesOf, getTypesEnvironment(getBreakState(fenv)));
					exitAcquireActions += getAcquireActions(getBreakState(fenv));
					fenv = updateBreak(fenv,emptyState());
					
					currentStmts = stmts;
					currentEnv = merge(env, currentEnv);
					currentTypesOf = mergeTypesEnvironment(typesOf, currentTypesOf);
					currentAcquireActions += acquireActions;
				}		
				exitFenv = mergeFlow(exitFenv, fenv);
				exs = mergeExceptions(exs, exsC);
				currentCase = [];			
			}
			case  \defaultCase():{
				hasDefault = true;
				<currentStmts, currentEnv, currentTypeOf, currentAcquireActions, fenv, exsC> = gatherStmtFromStatements(\block(currentCase), currentEnv, currentTypesOf, volatileFields, currentAcquireActions, currentStmts);
				if(isEmpty(getBreakState(fenv))){
					currentEnv = merge(env, currentEnv);
					currentTypesOf = mergeTypesEnvironment(typesOf, currentTypesOf);
				}
				else{
					exitStmts += currentStmts;
					exitEnv = merge(exitEnv, getEnvironment(getBreakState(fenv)));
					exitTypesOf = mergeTypesEnvironment(exitTypesOf, getTypesEnvironment(getBreakState(fenv)));
					exitAcquireActions += getAcquireActions(getBreakState(fenv));
					fenv = updateBreak(fenv,emptyState());
					
					currentStmts = stmts;
					currentEnv = merge(env, currentEnv);
					currentTypesOf = mergeTypesEnvironment(typesOf, currentTypesOf);
					currentAcquireActions += acquireActions;
				}		
				exitFenv = mergeFlow(exitFenv, fenv);
				exs = mergeExceptions(exs, exsC);
				currentCase = [];
			}
			default:{
				currentCase += [stmt];
			}
		}
	}
	<currentStmts, currentEnv, currentTypeOf, currentAcquireActions, fenv, exsC> = gatherStmtFromStatements(\block(currentCase), currentEnv, currentTypesOf, volatileFields, currentAcquireActions, currentStmts);
	exitStmts += currentStmts;
	exitEnv = merge(exitEnv, currentEnv);
	exitEnv = merge(exitEnv,getEnvironment(getBreakState(fenv)));
	exitTypesOf = mergeTypesEnvironment(exitTypesOf, currentTypeOf);
	exitTypesOf = mergeTypesEnvironment(exitTypesOf, getTypesEnvironment(getBreakState(fenv)));
	exitAcquireActions += currentAcquireActions;
	exitAcquireActions += getAcquireActions(getBreakState(fenv));
	fenv = updateBreak(fenv,emptyState());
	exitFenv = mergeFlow(exitFenv, fenv);
	exs = mergeExceptions(exs, exsC);
	if(!hasDefault){
		exitEnv = merge(exitEnv, env);
		exitTypeOf = mergeTypesEnvironment(exitTypesOf, typesOf);
	}		
	return <exitStmts, exitEnv, exitTypesOf, exitAcquireActions, exitFenv, exs>;
}

//synchronizedStatement(Expression lock, Statement body)
tuple[set[Stmt], map[loc, set[loc]], map[loc,TypeSensitiveEnvironment], rel[loc,loc], FlowEnvironment, map[str, State]] gatherStmtFromStatements(Statement s:synchronizedStatement(l, body), map[loc, set[loc]] env, map[loc,TypeSensitiveEnvironment] typesOf, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	println(l);
	<stmts, potential, env, typesOf, acquireActions, exs> = gatherStmtFromExpressions(l, env, typesOf, volatileFields, acquireActions, stmts);
	stmts += potential;
	acquireActions += extractAcquireActions(potential, volatileFields);
	
	loc vlock;
	println(potential);
	for(w:read(_, name, _) <- potential){
		vlock = name;
	}
	
	<stmts, env, typesOf, acquireActions, fenv, exsC> = gatherStmtFromStatements(body, env, typesOf, volatileFields, {<s@src, vlock>} + acquireActions, stmts);
	
	stmts += addAndUnlock(stmts, s@src, vlock);
	exs = mergeExceptions(exs, exsC);
	return <stmts, env, typesOf, acquireActions, fenv, exs>;
}

//throw(Expression exp)
tuple[set[Stmt], map[loc, set[loc]], map[loc,TypeSensitiveEnvironment], rel[loc,loc], FlowEnvironment, map[str, State]] gatherStmtFromStatements(Statement s:\throw(exp), map[loc, set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	exs = (extractClassName(exp@decl) : state(env, typesOf, acquireActions));
	return <stmts, (), (), {}, emptyFlowEnvironment(), exs>;
}

//\try(Statement body, list[Statement] catchClauses)
tuple[set[Stmt], map[loc, set[loc]], map[loc,TypeSensitiveEnvironment], rel[loc,loc], FlowEnvironment, map[str, State]] gatherStmtFromStatements(Statement s:\try(body, catchStatements), map[loc, set[loc]] env, map[loc,TypeSensitiveEnvironment] typesOf, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	<stmts, exitEnv, exitTypesOf, exitAcquireActions, exitFenv, exs> = gatherStmtFromStatements(body, env, typesOf, volatileFields, acquireActions, stmts);
	exitStmts = stmts; 
	exitExs = ();
	for(cs <- catchStatements){
		<stmtsC, envC, typesOfC, acquireActionsC, fenvC, exs, exsC> = gatherStmtFromCatchStatements(cs, volatileFields, exs, stmts);	
		exitStmts += stmtsC;
		exitEnv = merge(exitEnv, envC);
		exitTypesOf = mergeTypesEnvironment(exitTypesOf, typesOfC);
		exitAcquireActions += acquireActionsC;
		exitExs = mergeExceptions(exitExs,exsC);
		exitFenv = mergeFlow(exitFenv, fenvC);
	}
	exitExs = mergeExceptions(exitExs,exs);
	return <exitStmts, exitEnv, exitTypesOf, exitAcquireActions, exitFenv, exitExs>;
}

//\try(Statement body, list[Statement] catchClauses, Statement \finally) 
tuple[set[Stmt], map[loc, set[loc]], map[loc,TypeSensitiveEnvironment], rel[loc,loc], FlowEnvironment, map[str, State]] gatherStmtFromStatements(Statement s:\try(body, catchStatements, fin), map[loc, set[loc]] env, map[loc,TypeSensitiveEnvironment] typesOf, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){ 
	<stmts, exitEnv, exitTypesOf, exitAcquireActions, exitFenv, exs> = gatherStmtFromStatements(body, env, typesOf, volatileFields, acquireActions, stmts);
	exitStmts = stmts; 
	exitExs = ();
	for(cs <- catchStatements){
		<stmtsC, envC, typesOfC, acquireActionsC, fenvC, exs, exsC> = gatherStmtFromCatchStatements(cs, volatileFields, exs, stmts);	
		exitStmts += stmtsC;
		exitEnv = merge(exitEnv, envC);
		exitTypesOf = mergeTypesEnvironment(exitTypesOf, typesOfC);
		exitAcquireActions += acquireActionsC;
		exitExs = mergeExceptions(exitExs,exsC);
		exitFenv = mergeFlow(exitFenv, fenvC);
	}
	exitExs = mergeExceptions(exitExs,exs);
	//Run finally for every environemnt
	//exit
	<finStmts, exitEnv, exitTypesOf, exitAcquireActions, fenv,  exsE> = gatherStmtFromStatements(fin, exitEnv, exitTypesOf, volatileFields, exitAcquireActions, exitStmts);
	exitExs = mergeExceptions(exitExs, exsE);
	//continue
	<stmts, envC, typesOfC, acquireActionsC, fenvC, exsC> = gatherStmtFromStatements(fin, getEnvironment(getContinueState(exitFenv)), getTypesEnvironment(getContinueState(exitFenv)), volatileFields, getAcquireActions(getContinueState(exitFenv)), exitStmts);
	finStmts += stmts;
	fenv = updateContinue(fenv, state(envC, typesOfC, acquireActionsC));
	fenv = mergeFlow(fenv, fenvC);
	exitExs = mergeExceptions(exitExs, exsC);
	//break
	<stmts, envB, typesOfB, acquireActionsB, fenvB, exsB> = gatherStmtFromStatements(fin, getEnvironment(getBreakState(exitFenv)), getTypesEnvironment(getBreakState(exitFenv)), volatileFields, getAcquireActions(getBreakState(exitFenv)), exitStmts);
	finStmts += stmts;
	fenv = updateBreak(fenv, state(envB, typesOfB, acquireActionsB));
	fenv = mergeFlow(fenv, fenvB);
	exitExs = mergeExceptions(exitExs, exsB);
	//return
	<stmts, envR, typesOfR, acquireActionsR, fenvR, exsR> = gatherStmtFromStatements(fin, getEnvironment(getReturnState(exitFenv)), getTypesEnvironment(getReturnState(exitFenv)), volatileFields, getAcquireActions(getReturnState(exitFenv)), exitStmts);
	finStmts += stmts;
	fenv = updateReturn(fenv, state(envR, typesOfR, acquireActionsR));
	fenv = mergeFlow(fenv, fenvR);
	exitExs = mergeExceptions(exitExs, exsR);
	return <finStmts, exitEnv, exitTypesOf, exitAcquireActions, fenv, exitExs>;
}

//\catch(Declaration exception, Statement body)
tuple[set[Stmt], map[loc, set[loc]], map[loc,TypeSensitiveEnvironment], rel[loc,loc], FlowEnvironment, map[str, State], map[str, State]] gatherStmtFromCatchStatements(Statement s:\catch(except, body), set[loc] volatileFields, map[str, State] exs, set[Stmt] stmts){
	env = ();
	fenv = emptyFlowEnvironment();
	map[str, State] exsCatch = ();
	map[loc, TypeSensitiveEnvironment] typesOf = ();
	rel[loc,loc] acquireActions = {};
	visit(except){
		case e:simpleName(_) : {
			<exceptionState, exs> = getAndRemoveState(exs, e@decl.path);
			if(!isEmpty(exceptionState)){
				<stmts, envCatch, typesOfCatch, acquireActionsCatch, fenvCatch, exsC> = gatherStmtFromStatements(body, getEnvironment(exceptionState), getTypesEnvironment(exceptionState), volatileFields, getAcquireActions(exceptionState), stmts);
				env = merge(env,envCatch);
				typesOf = mergeTypesEnvironment(typesOf, typesOfCatch);
				exsCatch = mergeExceptions(exsCatch, exsC);
				fenv = mergeFlow(fenv, fenvCatch);
				acquireActions += acquireActionsCatch;
			}
			else{
				println("Unreached exception, <e@src>");
			}
		}
	}
	return <stmts, env, typesOf, acquireActions, fenv, exs, exsCatch>;
}

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

//\while(Expression condition, Statement body)
tuple[set[Stmt], map[loc, set[loc]], map[loc, TypeSensitiveEnvironment], rel[loc,loc], FlowEnvironment, map[str, State]] gatherStmtFromStatements(Statement s:\while(cond, body), map[loc, set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	<stmts, potential, env, typesOf, acquireActions, exs> = gatherStmtFromExpressions(cond, env, typesOf, volatileFields, acquireActions, stmts);
	stmts += potential;
	acquireActions += extractAcquireActions(potential, volatileFields);
	exitEnv = env;
	exitTypesOf = typesOf;
	exitAcquireActions = acquireActions;
	exitExs = exs;
	
	<stmts, envB, typesOfB, acquireActionsB, fenvB, exsB> = gatherStmtFromStatements(body, env, typesOf, volatileFields, acquireActions, stmts);
	exitEnv = merge(exitEnv, getEnvironment(getBreakState(fenvB)));
	exitTypesOf = mergeTypesEnvironment(exitTypesOf, getTypesEnvironment(getBreakState(fenvB)));
	exitAcquireActions += getAcquireActions(getBreakState(fenvB));
	exitExs = mergeExceptions(exitExs, exsB);

	envB = merge(envB, getEnvironment(getContinueState(fenvB)));
	typesOfB = mergeTypesEnvironment(exitTypesOf, getTypesEnvironment(getContinueState(fenvB)));
	acquireActionsB += getAcquireActions(getContinueState(fenvB));
	
	<stmts, potential, env, typesOf, acquireActions, exs> = gatherStmtFromExpressions(cond, envB, typesOfB, volatileFields, acquireActionsB, stmts);
	stmts += potential;
	exitExs = mergeExceptions(exitExs, exs);
	
	exitEnv = merge(exitEnv, env);
	exitTypesOf = mergeTypesEnvironment(exitTypesOf, typesOf);
	exitAcquireActions += getAcquireActions(getBreakState(fenvB));
	
	<stmts, _, _, _, fenvB, exs> = gatherStmtFromStatements(body, env, typesOf, volatileFields, acquireActions, stmts);
	exitEnv = mergeNestedEnvironment(exitEnv, getEnvironment(getBreakState(fenvB)));
	exitTypesOf = mergeTypesEnvironment(exitTypesOf, getTypesEnvironment(getBreakState(fenvB)));
	exitAcquireActions += getAcquireActions(getBreakState(fenvB));
	exitExs = mergeExceptions(exitExs, exsB);
	
	return <stmts, exitEnv, exitTypesOf,  exitAcquireActions, initializeReturnState(getReturnState(fenvB)), exs>;
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

tuple[set[Stmt], map[loc, set[loc]], map[loc,TypeSensitiveEnvironment], rel[loc,loc], FlowEnvironment, map[str, State]] gatherStmtFromStatements(Statement b:empty(), map[loc, set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts)
	= <stmts, env, typesOf, acquireActions, emptyFlowEnvironment(), exs>;

default tuple[set[Stmt], map[loc, set[loc]], map[loc, TypeSensitiveEnvironment], rel[loc,loc], FlowEnvironment, map[str, State]] gatherStmtFromStatements(Statement b, map[loc, set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	println("case I do not need : <b>");
	return <stmts, env, typesOf, acquireActions, emptyFlowEnvironment(), ()>;
}

bool breakingControlFlow(Statement s:\continue()) = true;
bool breakingControlFlow(Statement s:\break()) = true;
bool breakingControlFlow(Statement s:\break("")) = true;
bool breakingControlFlow(Statement s:\return()) = true;
bool breakingControlFlow(Statement s:\return(_)) = true;
bool breakingControlFlow(Statement s:\throw(_)) = true;
default bool breakingControlFlow(Statement s) =  false;

