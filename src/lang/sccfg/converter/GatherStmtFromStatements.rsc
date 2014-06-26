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

//assert(Expression expression)
tuple[set[Stmt], map[loc,set[loc]], FlowEnvironment, rel[loc,loc],  map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:\assert(exp), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	return gatherStmtFromStatements(m, \assert(exp, Expression::null()), env, volatileFields, acquireActions, stmts);
}

//assert(Expression expression, Expression message)
tuple[set[Stmt], map[loc,set[loc]], FlowEnvironment, rel[loc,loc],  map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:\assert(exp, message), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	<stmts, potential, env, exs> = gatherStmtFromExpressions(m, exp, env, volatileFields, acquireActions, stmts);
	stmts += potential;
	acquireActions += extractAcquireAction(potential, volatileFields);
	
	<stmts, potential, envM, exsM> = gatherStmtFromExpressions(m, message, env, volatileFields, acquireActions, stmts);
	stmts += potential;
	exs = mergeExceptions(exs, exsM);
	//the volatile access from the message are not counted since if the message appears nothing else is going to be executed
	//The assert is a possible an exit point, in case of finally we can see it as a return
	env = mergeNestedEnvironment(env,envM);
	return <stmts, env, initializeReturnEnvironment(env), acquireActions, exs>;
}

//block(list[Statement] statements)
tuple[set[Stmt], map[loc,set[loc]], FlowEnvironment, rel[loc,loc],  map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:\block(sB), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	envInner = env;
	exs = ();
	fenv = emptyFlowEnvironment();
	for(stmt <- sB){
		<stmts, envInner, fenvS, acquireActions, exs> = gatherStmtFromStatements(m, stmt, envInner, volatileFields, acquireActions, stmts);
		fenv = mergeFlow(fenv, fenvS);
	}
	env = updateEnvironment(env, envInner);
	return <stmts, env, fenv, acquireActions, exs>;
}

//break()
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc],  map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:\break(), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	return <stmts, env, initializeBreakEnvironment(env), acquireActions, ()>;
}

//break("")
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc],  map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:\break(""), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	// ISSUE: what if break is not in a branch? then it is perceived partly as a continue
	return <stmts, env, initializeBreakEnvironment(env), acquireActions, ()>;
}

//break(str label)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc],  map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:\break(_), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	assert false : "Labeled statement (break) found!!!";
	return <stmts, env, initializeBreakEnvironment(env), acquireActions, ()>;
}

//continue()
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc],  map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:\continue(), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	return <stmts, env, initializeContinueEnvironment(env), acquireActions, ()>;
}

//continue(str label)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc],  map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:\continue(_), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	assert false : "Labeled statement (continue) found!!!";
	return <stmts, env, initializeContinueEnvironment(env), acquireActions, ()>;
}

//do(Statement body, Expression condition)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc],  map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:\do(b, cond), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
		
	//executed once all the reads and assigns added missing connections to itself
	<stmts, env, fenvInner, acquireActions, exs> = gatherStmtFromStatements(m, b, env, volatileFields, acquireActions, stmts);
			
	//include continue
	env = mergeNestedEnvironment(env, getContinueEnvironment(fenvInner));
			
	//running the condition after one loop getting all the connections from statements and continue command
	<stmts, potential, env, acquireActions, exsC> = gatherStmtFromExpressions(m, cond, env, volatileFields, acquireActions, stmts);
	exs = mergeExceptions(exs, exsC);
	stmts += potential;
	acquireActions += extractAcquireActions(potential, volatileFields);
	
	//connect the statements with the condition but the environment and exception are already found
	<stmts, env, _, exsC> = gatherStmtFromStatements(m, b, env, volatileFields, acquireActions, stmts);

	env = mergeNestedEnvironment(env, getBreakEnvironment(fenvInner));
	
	return <stmts, env, emptyFlowEnvironment(), acquireActions, exs>;
}

//foreach(Declaration parameter, Expression collection, Statement body)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc],  map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:\foreach(parameter, collection, body), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
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
	exs = mergeExceptions(exs,exsC);		
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
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc],  map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:\for(initializers, cond, updaters, body), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	return dealWithLoopsConditionFirst(m, initializers, cond, updaters, body, env, volatileFields, acquireActions, stmts);
} 

//for(list[Expression] initializers, list[Expression] updaters, Statement body)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc],  map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:\for(initializers, updaters, body), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	return dealWithLoopsConditionFirst(m, initializers, Expression::\null(), updaters, body, env, volatileFields, acquireActions, stmts);
}

//expressionStatement(Expression stmt)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc],  map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:\expressionStatement(e), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	<stmts, potential, env, acquireActions, exs> = gatherStmtFromExpressions(m, e, env, volatileFields, acquireActions, stmts);
	return <stmts, env, emptyFlowEnvironment(), acquireActions, exs>;
}

//if(Expression condition, Statement thenB)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc],  map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:\if(cond, thenB), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	<stmts, potential, env, acquireActions, exs> = gatherStmtFromExpressions(m, cond, env, volatileFields, acquireActions, stmts);
	stmts += potential;
	acquireActions += extractAcquireActions(potential, volatileFields);
	
	<stmts, envOpt, fenv, acquireActions, exsC> = gatherStmtFromStatements(m, thenB, env, volatileFields, acquireActions, stmts);
	exs = mergeExceptions(exs,exsC);			

	env = mergeNestedEnvironment(env,envOpt);
	return <stmts, env, fenv, acquireActions, exs>;
}

//if(Expression condition, Statement thenB, Statement elseB)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc],  map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:\if(cond, thenB, elseB), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	<stmts, potential, env, acquireActions, exs> = gatherStmtFromExpressions(m, cond, env, volatileFields, acquireActions, stmts);
	stmts += potential;
	acquireActions += extractAcquireActions(potential, volatileFields);
	
	<stmts, env, fenv, acquireActions, exsC> = branching(m, thenB, elseB, env, volatileFields, acquireActions, stmts); 
	return <stmts, env, fenv, merge(exs, exsC)>;
}

//label(str name, Statement body)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc],  map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:\label(_, _), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	assert false: "Labeled block";
	return <stmts, env, emptyFlowEnvironment(), acquireActions, ()>;
}

//return(Expression expression)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc],  map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:\return(exp), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	<stmts, potential, env, exs> = gatherStmtFromExpressions(m, exp, env, locks, stmts);
	stmts += potential;
	acquireActions += extractAcquireActions(potential, volatileFields); //needed for the finally
	return <stmts, env, initializeReturnEnvironment(env), acquireActions, exs>;
}

//return()
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc],  map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:\return(), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	return <stmts, env, initializeReturnEnvironment(env), acquireActions, exs>;
}

//switch(Expression exp, list[Statement] statements)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc],  map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:\switch(exp, body), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	<stmts, potential, env, exs> = gatherStmtFromExpressions(m, exp, env, locks, stmts);
	stmts += potential;
	acquireActions += extractAcquireActions(potential, volatileFields);
	
	outerEnv = env;
	rel[loc,loc] outerAcquireActions = {};
	rel[loc,loc] currentAcquireActions = outerAcquireActions;
	exitEnv = ();
	fenv = emptyFlowEnvironment();
	
	list[Statement] currentCase = [];
	hasDefault = false;
	for(stmt <- body){
		switch(stmt){
			case \case(_):{
				<stmts, currentEnv, fenvInner, currentAcquireActions, exsC> = gatherStmtFromStatements(m, \block(currentCase), currentEnv, volatileFields, currentAcquireActions, stmts);
				acquireActions += currentAcquireActions;
				exs = mergeExceptions(exs, exsC);
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
				exs = mergeExceptions(exs, exsC);
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
	exs = mergeExceptions(exs, exsC);
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
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc],  map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:synchronizedStatement(l, body), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	<stmts, potential, env, acquireActions, exs> = gatherStmtFromExpressions(m, l, env, volatileFields, acquireActions, stmts);
	stmts += potential;
	acquireActions += extractAcquireActions(potential, volatileFields);
	
	vlock = getDeclFromRead(getOneFrom(potential));	
	
	<stmts, env, fenv, acquireActions, exsC> = gatherStmtFromStatements(m, body, env, volatileFields, [<s@src, vlock>] + acquireActions, stmts); //order is important every lock is locked to the next ones
	
	stmts += addAndUnlock(stmts, s@src, vlock);//release
	exs = mergeExceptions(exs, exsC);
	return <stmts, env, fenv, acquireActions, exsC>;
}

//throw(Expression exp)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc],  map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:\throw(exp), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	exs = (extractClassName(exp@decl) : env);
	return <stmts, env, emptyFlowEnnvironment(), acquireActions, exs>;
}

//\try(Statement body, list[Statement] catchClauses)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc],  map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:\try(body, catchStatements), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	<stmts, env, fenv, acquireActions, exsInner> = gatherStmtFromStatements(m, body, env, volatileFields, acquireActions, stmts);	
	env = updateEnvironment(env, envTry);
	exitEnv = env;	
	exs = ();
	outerAcquireActions = acquireActions;
	for(cs <- catchStatements){
		<stmts, envC, fenvC, acquireActionsC, exsC> = gatherStmtFromCatchStatements(m, cs, env, volatileFields, outerAcquireActions, exsInner, stmts);	
		acquireActions += acquireActionsC;
		exs = mergeExceptions(exs,exsC);
		fenv = mergeFlow(fenv, fenvC);
		exitEnv = mergeNestedEnvironment(exitEnv, envC);
	}
	return <stmts, exitEnv, fenv, acquireActions, exs>;
}

//\try(Statement body, list[Statement] catchClauses, Statement \finally)  
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc],  map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:\try(body, catchStatements, fin), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	<stmts, envTry, fenv, acquireActions, exsInner> = gatherStmtFromStatements(m, body, env, volatileFields, acquireActions, stmts);
	env = updateEnvironment(env, envTry);	
	exitEnv = env;
	exs = ();
	
	outerAcquireActions = acquireActions;
	for(cs <- catchStatements){
		<stmts, envC, fenvC, acquireActionsC, exsC> = gatherStmtFromCatchStatements(m, catchStatements, env, volatileFields, outerAcquireActions, exsInner, stmts);	
		acquireActions += acquireActionsC;
		exs = mergeExceptions(exs,exsC);
		fenv = mergeFlow(fenv, fenvC);
		exitEnv = mergeNestedEnvironment(exitEnv, envC);
	}
	//Run finally for every environemnt
	//exit
	<stmts, exitEnv, fenvE, acquireActions, exsE> = gatherStmtFromStatements(m, fin, exitEnv, volatileFields, acquireActions, stmts);
	exs = mergeExceptions(exs,exsE);
	//continue
	<stmts, envC, _, _, _> = gatherStmtFromStatements(m, fin, getContinueEnvironment(fenv), volatileFields, acquireActions, stmts);
	fenv = updateContinue(fenv, envC);
	//break
	<stmts, envB, _, _, _> = gatherStmtFromStatements(m, fin, getBreakEnvironment(fenv), volatileFields, acquireActions, stmts);
	fenv = updateContinue(fenv, envB);
	//return
	<stmts, envR, _, _, _> = gatherStmtFromStatements(m, fin, getReturnEnvironment(fenv), volatileFields, acquireActions, stmts);
	fenv = updateReturn(fenv, envR);
	return <stmts, exitEnv, fenv, acquireActions, exs>;
}

//\catch(Declaration exception, Statement body)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc],  map[str, map[loc, set[loc]]]] gatherStmtFromCatchStatements(Declaration m, Statement s:\catch(except, body), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, map[str, map[loc, set[loc]]] exs, set[Stmt] stmts){
	envCatch = ();
	fenv = emptyFlowEnvironment();
	visit(except){
		case e:simpleName(_) : {
			if(e@decl.path in exs){
				<stmts, envC, fenvCatch, acquireActions, exsCatch> = gatherStmtFromStatements(m, body, updateEnvironment(env,exs[e@decl.path]), volatileFields, acquireActions, stmts);
				envCatch = mergeNestedEnvironment(env,envC);
				exs = merge(exs, exsCatch);
				fenv = mergeFlow(fenv, fenvCatch);
			}
			assert false : "unknown exception";
			//<stmts, envCatch, fenv, exsCatch> = gatherStmtFromStatements(m, updateEnvironment(env,envCatch), fenv, locks, stmts);
			//envCatch = merge(envCatch,env);
		}
	}
	return <stmts, mergeNestedEnvironment(env,envCatch), fenv, acquireActions, exsCatch>;
}

//\declarationStatement(Declaration declaration)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc],  map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:\declarationStatement(d), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	exs = ();
	fenv = emptyFlowEnvironment();
	top-down-break visit(d) {
		case Expression e : {
			<stmts, _, env, acquireActions, exsE> = gatherStmtFromExpressions(m, e, env, volatileFields, acquireActions, stmts);
			exs = mergeExceptions(exs, exsE);
		}
		case Statement s : {
			<stmts, env, fenvD, acquireActions, exsD> = gatherStmtFromStatements(m, s, env, volatileFields, acquireActions, stmts);
			exs = mergeExceptions(exs, exsD);
			fenv = mergeFlow(fenv, fenvD);
		}
	}
	return <stmts, env, fenv, acquireActions, exs>;
}


//\while(Expression condition, Statement body)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc],  map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:\while(cond, body), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	list[Expression] emptyList = [];
	return dealWithLoopsConditionFirst(m, emptyList, cond, emptyList, body, env, volatileFields, acquireActions, stmts);
}

//\expressionStatement(Expression stmt)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc],  map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:expressionStatement(e), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	<stmts, _, env, acquireActions, exs> = gatherStmtFromExpressions(m, e, env, volatileFields, acquireActions, stmts);
	return <stmts, env, emptyFlowEnvironment(), acquireActions, exs>;
}

 //\constructorCall(bool isSuper, Expression expr, list[Expression] arguments)
 tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc],  map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:constructorCall(isSuper, exp, args), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
 	exs = ();
	for(arg <- args){
		<stmts, potential, env, acquireActions, exsC> = gatherStmtFromExpressions(m, arg, env, volatileFields, acquireActions, stmts);
		stmts += potential;
		acquireActions += extractAcquireActions(potential, volatileFields);
		exs = mergeExceptions(exs,exsC);
	}
	<stmts, potential, env, acquireActions, exsC> = gatherStmtFromExpressions(m, exp, env, volatileFields, acquireActions, stmts);
	stmts += potential;
	acquireActions += extractAcquireActions(potential, volatileFields);
	exs = mergeExceptions(exs,exsC);
		
	return <stmts, env, emptyFlowEnvironment(), acquireActions, exs>;
}
 //\constructorCall(bool isSuper, list[Expression] arguments)
 tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc], map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:constructorCall(isSuper, args), map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	 return gatherStmtFromStatements(m, constructorCall(isSuper, Expression::null(), args), env, volatileFields, acquireActions, stmts);
 }


tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc], map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement b, map[loc, set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	println("case I do not need : <b>");
	return <stmts, env, emptyFlowEnvironment(), acquireActions, ()>;
}

loc getDeclFromRead(Stmt r:read(_, decl, _)) = decl;

