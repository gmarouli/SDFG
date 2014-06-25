module lang::sccfg::converter::GatherStmtFromStatements

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
import lang::sccfg::converter::Java2DFG;

//assert(Expression expression)
tuple[set[Stmt], map[loc,set[loc]], FlowEnvironment, map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:\assert(exp), map[loc, set[loc]] env, lrel[loc, loc] locks, set[Stmt] stmts){
	return gatherStmtFromStatements(m, \assert(exp, Expression::null()), env, locks, stmts);
}

//assert(Expression expression, Expression message)
tuple[set[Stmt], map[loc,set[loc]], FlowEnvironment, map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:\assert(exp, message), map[loc, set[loc]] env, lrel[loc, loc] locks, set[Stmt] stmts){
	<stmts, potential, env, exs> = gatherStmtFromExpressions(m, exp, env, locks, stmts);
	stmts = addAndLock(potential, locks, stmts);
	
	<stmts, potential, envM, exsM> = gatherStmtFromExpressions(m, message, env, locks, stmts);
	stmts = addAndLock(potential, locks, stmts);
	exs = mergeExceptions(exs, exsM);
	//The assert is a possible an exit point, in case of finally we can see it as a return
	env = mergeNestedEnvironment(env,envM);
	return <stmts, env, initializeReturnEnvironment(env), exs>;
}

//block(list[Statement] statements)
tuple[set[Stmt], map[loc,set[loc]], FlowEnvironment, map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:\block(sB), map[loc, set[loc]] env, lrel[loc, loc] locks, set[Stmt] stmts){
	envInner = env;
	exs = ();
	fenv = emptyFlowEnvironment();
	for(stmt <- sB){
		<stmts, envInner, fenvS, exs> = gatherStmtFromStatements(m, stmt, envInner, locks, stmts);
		fenv = mergeFlow(fenv, fenvS);
	}
	env = updateEnvironment(env, envInner);
	return <stmts, env, fenv, exs>;
}

//break()
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:\break(), map[loc, set[loc]] env, lrel[loc, loc] locks, set[Stmt] stmts){
	return <stmts, env, initializeBreakEnvironment(env), ()>;
}

//break("")
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:\break(""), map[loc, set[loc]] env, lrel[loc, loc] locks, set[Stmt] stmts){
	// ISSUE: what if break is not in a branch? then it is perceived partly as a continue
	return <stmts, env, initializeBreakEnvironment(env), ()>;
}

//break(str label)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:\break(_), map[loc, set[loc]] env, lrel[loc, loc] locks, set[Stmt] stmts){
	assert false : "Labeled statement (break) found!!!";
	return <stmts, env, initializeBreakEnvironment(env), ()>;
}

//continue()
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:\continue(), map[loc, set[loc]] env, lrel[loc, loc] locks, set[Stmt] stmts){
	return <stmts, env, initializeContinueEnvironment(env), ()>;
}

//continue(str label)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:\continue(_), map[loc, set[loc]] env, lrel[loc, loc] locks, set[Stmt] stmts){
	assert false : "Labeled statement (continue) found!!!";
	return <stmts, env, initializeContinueEnvironment(env), ()>;
}

//do(Statement body, Expression condition)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:\do(b, cond), map[loc, set[loc]] env, lrel[loc, loc] locks, set[Stmt] stmts){
		
	//executed once all the reads and assigns added missing connections to itself
	<stmts, env, fenvInner, exs> = gatherStmtFromStatements(m, b, env, locks, stmts);
			
	//include continue
	env = mergeNestedEnvironment(env, getContinueEnvironment(fenvInner));
			
	//running the condition after one loop getting all the connections from statements and continue command
	<stmts, potential, env, exsC> = gatherStmtFromExpressions(m, cond, env, locks, stmts);
	exs = mergeExceptions(exs, exsC);
	stmts += potential;
	
	//connect the statements with the condition but the environment and exception are already found
	<stmts, env, _, exsC> = gatherStmtFromStatements(m, b, env, locks, stmts);

	env = mergeNestedEnvironment(env, getBreakEnvironment(fenvInner));
	
	return <stmts, env, emptyFlowEnvironment(), exs>;
}

//foreach(Declaration parameter, Expression collection, Statement body)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:\foreach(parameter, collection, body), map[loc, set[loc]] env, lrel[loc, loc] locks, set[Stmt] stmts){
	outerEnv = env;
	<stmts, potential, env, exs> = gatherStmtFromExpressions(m, collection, env, locks, stmts);
	stmts = addAndLock(potential + {Stmt::assign(s@src, parameter@decl, s@src)}, locks, stmts);
	env[parameter@decl] = {s@src};
	
	outerEnv = updateEnvironment(outerEnv, env);
	
	//executed once all the reads and assigns added missing connections to itself
	<stmts, env, fenvInner, exsC> = gatherStmtFromStatements(m, b, env, locks, stmts);
	exs = mergeExceptions(exs,exsC);		
	//include continue
	env = mergeNestedEnvironment(env, getContinueEnvironment(fenvInner));
			
	//running the condition after one loop getting all the connections from statements and continue command
	<stmts, potential, env, _> = gatherStmtFromExpressions(m, collection, env, locks, stmts);
	stmts = addAndLock(potential, locks, stmts);
	
	//connect the statements with the condition but the environment and exception are already found
	<stmts, env, _, _> = gatherStmtFromStatements(m, b, env, locks, stmts);

	env = mergeNestedEnvironment(env, getBreakEnvironment(fenvInner));
	
	return <stmts, mergeNestedEnvironment(outerEnv,env), emptyFlowEnvironment(), exs>;
}

//for(list[Expression] initializers, Expression condition, list[Expression] updaters, Statement body)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:\for(initializers, cond, updaters, body), map[loc, set[loc]] env, lrel[loc, loc] locks, set[Stmt] stmts){
	return dealWithLoopsConditionFirst(m, initializers, cond, updaters, body, env, locks, stmts);
} 

//for(list[Expression] initializers, list[Expression] updaters, Statement body)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:\for(initializers, updaters, body), map[loc, set[loc]] env, lrel[loc, loc] locks, set[Stmt] stmts){
	return dealWithLoopsConditionFirst(m, initializers, Expression::\null(), updaters, body, env, locks, stmts);
}

//expressionStatement(Expression stmt)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:\expressionStatement(e), map[loc, set[loc]] env, lrel[loc, loc] locks, set[Stmt] stmts){
	<stmts, potential, env, exs> = gatherStmtFromExpressions(m, e, env, locks, stmts);
	return <stmts, env, emptyFlowEnvironment(), exs>;
}

//if(Expression condition, Statement thenB)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:\if(cond, thenB), map[loc, set[loc]] env, lrel[loc, loc] locks, set[Stmt] stmts){
	<stmts, potential, env, exs> = gatherStmtFromExpressions(m, cond, env, locks, stmts);
	stmts = addAndLock(potential, locks, stmts);
	<stmts, envOpt, fenv, exsC> = gatherStmtFromStatements(m, thenB, env, locks, stmts);
	exs = mergeExceptions(exs,exsC);			

	env = mergeNestedEnvironment(env,envOpt);
	return <stmts, env, fenv, exs>;
}

//if(Expression condition, Statement thenB, Statement elseB)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:\if(cond, thenB, elseB), map[loc, set[loc]] env, lrel[loc, loc] locks, set[Stmt] stmts){
	<stmts, potential, env, exs> = gatherStmtFromExpressions(m, cond, env, locks, stmts);
	stmts = addAndLock(potential, locks, stmts);
	<stmts, env, fenv, exsC> = branching(m, thenB, elseB, env, locks, stmts); 
	return <stmts, env, fenv, merge(exs, exsC)>;
}

//label(str name, Statement body)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:\label(_, _), map[loc, set[loc]] env, lrel[loc, loc] locks, set[Stmt] stmts){
	assert false: "Labeled block";
	return <stmts, env, emptyFlowEnvironment(), ()>;
}

//return(Expression expression)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:\return(exp), map[loc, set[loc]] env, lrel[loc, loc] locks, set[Stmt] stmts){
	<stmts, potential, env, exs> = gatherStmtFromExpressions(m, exp, env, locks, stmts);
	stmts = addAndLock(potential, locks, stmts);
	return <stmts, env, initializeReturnEnvironment(env), exs>;
}

//return()
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:\return(), map[loc, set[loc]] env, lrel[loc, loc] locks, set[Stmt] stmts){
	return <stmts, env, initializeReturnEnvironment(env), exs>;
}

//switch(Expression exp, list[Statement] statements)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:\switch(exp, body), map[loc, set[loc]] env, lrel[loc, loc] locks, set[Stmt] stmts){
	<stmts, potential, env, exs> = gatherStmtFromExpressions(m, exp, env, locks, stmts);
	stmts = addAndLock(potential, locks, stmts);
	
	outerEnv = env;
	exitEnv = ();
	fenv = emptyFlowEnvironment();
	
	list[Statement] currentCase = [];
	hasDefault = false;
	for(stmt <- body){
		switch(stmt){
			case \case(_):{
				<stmts, currentEnv, fenvInner, exsC> = gatherStmtFromStatements(m, \block(currentCase), currentEnv, locks, stmts);
				exs = mergeExceptions(exs, exsC);
				fenv = mergeFlow(fenv, fenvInner);
				currentCase = [];
						
				if(getBreakEnvironment(fenvInner) != ()){
					exitEnv = merge(exitEnv, getBreakEnvironment(fenvInner));
					currentEnv = outerEnv;
				}
				else{
					currentEnv = updateEnvironment(outerEnv, currentEnv);
				}
			}
			case  \defaultCase():{
				hasDefault = true;
				<stmts, currentEnv, fenvInner, exsC> = gatherStmtFromStatements(m, \block(currentCase), currentEnv, locks, stmts);
				exs = mergeExceptions(exs, exsC);
				fenv = mergeFlow(fenv, fenvInner);
				currentCase = [];
							
				if(getBreakEnvironment(fenvInner) != ()){
					exitEnv = merge(exitEnv, getBreakEnvironment(fenvInner));
					currentEnv = outerEnv;
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

	<stmts, currentEnv, fenvInner, exsC> = gatherStmtFromStatements(m, \block(currentCase), currentEnv, locks, stmts);
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
	return <stmts, env, flowEnvironment(getContinueEnvironment(fenv), (), getReturnEnvironment(fenv)), exs>;
}

//synchronizedStatement(Expression lock, Statement body)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:synchronizedStatement(l, body), map[loc, set[loc]] env, lrel[loc, loc] locks, set[Stmt] stmts){
	<stmts, potential, env, exs> = gatherStmtFromExpressions(m, l, env, locks, stmts);
	stmts = addAndLock(potential, locks, stmts);
	vlock = getDeclFromRead(getOneFrom(potential));	
	<stmts, env, fenv, exsC> = gatherStmtFromStatements(m, body, env, [<s@src, vlock>] + locks, stmts); //order is important every lock is locked to the next ones
	exs = mergeExceptions(exs, exsC);
	return <stmts, env, fenv, exsC>;
}

//throw(Expression exp)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:\throw(exp), map[loc, set[loc]] env, lrel[loc, loc] locks, set[Stmt] stmts){
	exs = (extractClassName(exp@decl) : env);
	return <stmts, env, emptyFlowEnnvironment(), exs>;
}

//\try(Statement body, list[Statement] catchClauses)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:\try(body, catchStatements), map[loc, set[loc]] env, lrel[loc, loc] locks, set[Stmt] stmts){
	<stmts, env, fenv, exsInner> = gatherStmtFromStatements(m, body, env, locks, stmts);	
	env = updateEnvironment(env, envTry);
	exitEnv = env;	
	exs = ();
	for(cs <- catchStatements){
		<stmts, envC, fenvC, exsC> = gatherStmtFromCatchStatements(m, cs, env, locks, exsInner, stmts);	
		exs = mergeExceptions(exs,exsC);
		fenv = mergeFlow(fenv, fenvC);
		exitEnv = mergeNestedEnvironment(exitEnv, envC);
	}
	return <stmts, exitEnv, fenv, exs>;
}

//\try(Statement body, list[Statement] catchClauses, Statement \finally)  
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:\try(body, catchStatements, fin), map[loc, set[loc]] env, lrel[loc, loc] locks, set[Stmt] stmts){
	<stmts, envTry, fenv, exsInner> = gatherStmtFromStatements(m, body, env, locks, stmts);
	env = updateEnvironment(env, envTry);	
	exitEnv = env;
	exs = ();
	
	for(cs <- catchStatements){
		<stmts, envC, fenvC, exsC> = gatherStmtFromCatchStatements(m, catchStatements, env, locks, exsInner, stmts);	
		exs = mergeExceptions(exs,exsC);
		fenv = mergeFlow(fenv, fenvC);
		exitEnv = mergeNestedEnvironment(exitEnv, envC);
	}
	//Run finally for every environemnt
	//exit
	<stmts, exitEnv, fenvE, exsE> = gatherStmtFromStatements(m, fin, exitEnv, locks, stmts);
	exs = mergeExceptions(exs,exsE);
	//continue
	<stmts, envC, _, _> = gatherStmtFromStatements(m, fin, getContinueEnvironment(fenv), locks, stmts);
	fenv = updateContinue(fenv, envC);
	//break
	<stmts, envB, _, _> = gatherStmtFromStatements(m, fin, getBreakEnvironment(fenv), locks, stmts);
	fenv = updateContinue(fenv, envB);
	//return
	<stmts, envR, _, _> = gatherStmtFromStatements(m, fin, getReturnEnvironment(fenv), locks, stmts);
	fenv = updateReturn(fenv, envR);
	return <stmts, exitEnv, fenv, exs>;
}

//\catch(Declaration exception, Statement body)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[str, map[loc, set[loc]]]] gatherStmtFromCatchStatements(Declaration m, Statement s:\catch(except, body), map[loc, set[loc]] env, lrel[loc, loc] locks, map[str, map[loc, set[loc]]] exs, set[Stmt] stmts){
	envCatch = ();
	fenv = emptyFlowEnvironment();
	visit(except){
		case e:simpleName(_) : {
			if(e@decl.path in exs){
				<stmts, envC, fenvCatch, exsCatch> = gatherStmtFromStatements(m, body, updateEnvironment(env,exs[e@decl.path]), locks, stmts);
				envCatch = mergeNestedEnvironment(env,envC);
				exs = merge(exs, exsCatch);
				fenv = mergeFlow(fenv, fenvCatch);
			}
			assert false : "unknown exception";
			//<stmts, envCatch, fenv, exsCatch> = gatherStmtFromStatements(m, updateEnvironment(env,envCatch), fenv, locks, stmts);
			//envCatch = merge(envCatch,env);
		}
	}
	return <stmts, mergeNestedEnvironment(env,envCatch), fenv, exsCatch>;
}

//\declarationStatement(Declaration declaration)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:\declarationStatement(d), map[loc, set[loc]] env, lrel[loc, loc] locks, set[Stmt] stmts){
	exs = ();
	fenv = emptyFlowEnvironment();
	top-down-break visit(d) {
		case Expression e : {
			<stmts, _, env, exsE> = gatherStmtFromExpressions(m, e, env, locks, stmts);
			exs = mergeExceptions(exs, exsE);
		}
		case Statement s : {
			<stmts, env, fenvD, exsD> = gatherStmtFromStatements(m, s, env, locks, stmts);
			exs = mergeExceptions(exs, exsD);
			fenv = mergeFlow(fenv, fenvD);
		}
	}
	return <stmts, env, fenv, exs>;
}


//\while(Expression condition, Statement body)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:\while(cond, body), map[loc, set[loc]] env, lrel[loc, loc] locks, set[Stmt] stmts){
	list[Expression] emptyList = [];
	return dealWithLoopsConditionFirst(m, emptyList, cond, emptyList, body, env, locks, stmts);
}

//\expressionStatement(Expression stmt)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:expressionStatement(e), map[loc, set[loc]] env, lrel[loc, loc] locks, set[Stmt] stmts){
	<stmts, _, env, exs> = gatherStmtFromExpressions(m, e, env, locks, stmts);
	return <stmts, env, emptyFlowEnvironment(), exs>;
}

 //\constructorCall(bool isSuper, Expression expr, list[Expression] arguments)
 tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:constructorCall(isSuper, exp, args), map[loc, set[loc]] env, lrel[loc, loc] locks, set[Stmt] stmts){
 	exs = ();
	for(arg <- args){
		<stmts, potential, env, exsC> = gatherStmtFromExpressions(m, arg, env, locks, stmts);
		stmts = addAndLock(potential, locks, stmts);
		exs = mergeExceptions(exs,exsC);
	}
	<stmts, potential, env, exsC> = gatherStmtFromExpressions(m, exp, env, locks, stmts);
	exs = mergeExceptions(exs,exsC);
	stmts = addAndLock(potential, locks, stmts);
		
	return <stmts, env, emptyFlowEnvironment(), exs>;
}
 //\constructorCall(bool isSuper, list[Expression] arguments)
 tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:constructorCall(isSuper, args), map[loc, set[loc]] env, lrel[loc, loc] locks, set[Stmt] stmts){
	 return gatherStmtFromStatements(m, constructorCall(isSuper, Expression::null(), args), env, locks, stmts);
 }


tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement b, map[loc, set[loc]] env, lrel[loc, loc] locks, set[Stmt] stmts){
	println("case I do not need : <b>");
	return <stmts, env, emptyFlowEnvironment(), ()>;
}

loc getDeclFromRead(Stmt r:read(_, decl, _)) = decl;
