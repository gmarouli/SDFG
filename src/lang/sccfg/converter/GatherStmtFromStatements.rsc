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
//assert(Expression expression, Expression message)

//block(list[Statement] statements)
tuple[set[Stmt], map[loc,set[loc]], FlowEnvironment, map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:\block(sB), map[loc, set[loc]] env, FlowEnvironment fenv, rel[loc,loc] locks, set[Stmt] stmts){
	envInner = env;
	exs = ();
	for(stmt <- sB){
		<stmts, envInner, fenv, exs> = gatherStmtFromStatements(m, stmt, envInner, fenv, locks, stmts);
	}
	env = updateEnvironment(env, envInner);
	return <stmts, env, fenv, exs>;
}

//break()
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:\break(), map[loc, set[loc]] env, FlowEnvironment fenv, rel[loc,loc] locks, set[Stmt] stmts){
	return <stmts, env, mergeBreak(fenv, env), ()>;
}

//break("")
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:\break(""), map[loc, set[loc]] env, FlowEnvironment fenv, rel[loc,loc] locks, set[Stmt] stmts){
	// ISSUE: what if break is not in a branch? then it is perceived partly as a continue
	return <stmts, env, mergeBreak(fenv, env), ()>;
}

//break(str label)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:\break(_), map[loc, set[loc]] env, FlowEnvironment fenv, rel[loc,loc] locks, set[Stmt] stmts){
	assert false : "Labeled statement (break) found!!!";
	return <stmts, env, fenv, ()>;
}

//continue()
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:\continue(), map[loc, set[loc]] env, FlowEnvironment fenv, rel[loc,loc] locks, set[Stmt] stmts){
	return <stmts, env, mergeContinue(fenv, env), ()>;
}

//continue(str label)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:\continue(_), map[loc, set[loc]] env, FlowEnvironment fenv, rel[loc,loc] locks, set[Stmt] stmts){
	assert false : "Labeled statement (continue) found!!!";
	return <stmts, env, fenv, ()>;
}

//do(Statement body, Expression condition)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:\do(b, cond), map[loc, set[loc]] env, FlowEnvironment fenv, rel[loc,loc] locks, set[Stmt] stmts){
		
	//executed once all the reads and assigns added missing connections to itself
	<stmts, env, fenvInner, exs> = gatherStmtFromStatements(m, b, env, flowEnvironment((),()), locks, stmts);
			
	//include continue
	env = mergeNestedEnvironment(env, getContinueEnvironment(fenvInner));
			
	//running the condition after one loop getting all the connections from statements and continue command
	<stmts, potential, env, exsC> = gatherStmtFromExpressions(m, cond, env, locks, stmts);
	exs = mergeExceptions(exs, exsC);
	stmts += potential;
	
	//connect the statements with the condition but the environment and exception are already found
	<stmts, env, fenv, exsC> = gatherStmtFromStatements(m, b, env, fenvInner, locks, stmts);

	env = mergeNestedEnvironment(env, getBreakEnvironment(fenvInner));
	
	return <stmts, env, fenv, exs>;
}

//foreach(Declaration parameter, Expression collection, Statement body)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:\foreach(parameter, collection, body), map[loc, set[loc]] env, FlowEnvironment fenv, rel[loc,loc] locks, set[Stmt] stmts){
	outerEnv = env;
	<stmts, potential, env, exs> = gatherStmtFromExpressions(m, collection, env, locks, stmts);
	stmts += potential;
	stmts += {Stmt::assign(s@src, parameter@decl, s@src)};
	env[parameter@decl] = {s@src};
	
	outerEnv = updateEnvironment(outerEnv, env);
	
	//executed once all the reads and assigns added missing connections to itself
	<stmts, env, fenvInner, exsC> = gatherStmtFromStatements(m, b, env, flowEnvironment((),()), locks, stmts);
	exs = mergeExceptions(exs,exsC);		
	//include continue
	env = mergeNestedEnvironment(env, getContinueEnvironment(fenvInner));
			
	//running the condition after one loop getting all the connections from statements and continue command
	<stmts, potential, env, _> = gatherStmtFromExpressions(m, collection, env, locks, stmts);
	stmts += potential;
	
	//connect the statements with the condition but the environment and exception are already found
	<stmts, env, fenv, _> = gatherStmtFromStatements(m, b, env, fenvInner, locks, stmts);

	env = mergeNestedEnvironment(env, getBreakEnvironment(fenvInner));
	
	return <stmts, mergeNestedEnvironment(outerEnv,env), fenv, exs>;
}

//for(list[Expression] initializers, Expression condition, list[Expression] updaters, Statement body)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:\for(initializers, cond, updaters, body), map[loc, set[loc]] env, FlowEnvironment fenv, rel[loc,loc] locks, set[Stmt] stmts){
	return dealWithLoopsConditionFirst(m, initializers, cond, updaters, body, env, fenv, locks, stmts);
} 

//for(list[Expression] initializers, list[Expression] updaters, Statement body)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:\for(initializers, updaters, body), map[loc, set[loc]] env, FlowEnvironment fenv, rel[loc,loc] locks, set[Stmt] stmts){
	return dealWithLoopsConditionFirst(m, initializers, Expression::\null(), updaters, body, env, fenv, locks, stmts);
}

//expressionStatement(Expression stmt)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:\expressionStatement(e), map[loc, set[loc]] env, FlowEnvironment fenv, rel[loc,loc] locks, set[Stmt] stmts){
	<stmts, potential, env, exs> = gatherStmtFromExpressions(m, e, env, locks, stmts);
	return <stmts, env, fenv, exs>;
}

//if(Expression condition, Statement thenB)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:\if(cond, thenB), map[loc, set[loc]] env, FlowEnvironment fenv, rel[loc,loc] locks, set[Stmt] stmts){
	<stmts, potential, env, exs> = gatherStmtFromExpressions(m, cond, env, locks, stmts);
	stmts += potential;
	
	<stmts, envOpt, fenv, exsC> = gatherStmtFromStatements(m, thenB, env, fenv, locks, stmts);
	exs = mergeExceptions(exs,exsC);			

	env = mergeNestedEnvironment(env,envOpt);
	return <stmts, env, fenv, exs>;
}

//if(Expression condition, Statement thenB, Statement elseB)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:\if(cond, thenB, elseB), map[loc, set[loc]] env, FlowEnvironment fenv, rel[loc,loc] locks, set[Stmt] stmts){
	<stmts, potential, env, exs> = gatherStmtFromExpressions(m, cond, env, locks, stmts);
	stmts += potential;
	<stmts, env, fenv, exsC> = branching(m, thenB, elseB, env, fenv, locks, stmts); 
	return <stmts, env, fenv, merge(exs, exsC)>;
}

//label(str name, Statement body)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:\label(_, _), map[loc, set[loc]] env, FlowEnvironment fenv, rel[loc,loc] locks, set[Stmt] stmts){
	assert false: "Labeled block";
	return <stmts, env, fenv, ()>;
}

//return(Expression expression)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:\return(exp), map[loc, set[loc]] env, FlowEnvironment fenv, rel[loc,loc] locks, set[Stmt] stmts){
	<stmts, potential, env, exs> = gatherStmtFromExpressions(m, exp, env, locks, stmts);
	stmts += potential;
	return <stmts, env, fenv, exs>;
}

//return()
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:\return(), map[loc, set[loc]] env, FlowEnvironment fenv, rel[loc,loc] locks, set[Stmt] stmts){
	return <stmts, env, fenv, exs>;
}

//switch(Expression exp, list[Statement] statements)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:\switch(exp, body), map[loc, set[loc]] env, FlowEnvironment fenv, rel[loc,loc] locks, set[Stmt] stmts){
	<stmts, potential, env, exs> = gatherStmtFromExpressions(m, exp, env, locks, stmts);
	stmts += potential;
	
	outerEnv = env;
	exitEnv = ();
	fenvInner = flowEnvironment((),());
	
	list[Statement] currentCase = [];
	hasDefault = false;
	for(stmt <- body){
		switch(stmt){
			case \case(_):{
				<stmts, currentEnv, fenvInner, exsC> = gatherStmtFromStatements(m, \block(currentCase), currentEnv, fenvInner, locks, stmts);
				exs = mergeExceptions(exs, exsC);
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
				<stmts, currentEnv, fenvInner, exsC> = gatherStmtFromStatements(m, \block(currentCase), currentEnv, fenvInner, locks, stmts);
				exs = mergeExceptions(exs, exsC);
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

	<stmts, currentEnv, fenvInner, exsC> = gatherStmtFromStatements(m, \block(currentCase), currentEnv, fenv, locks, stmts);	
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
	return <stmts, env, fenv, exs>;
}

//synchronizedStatement(Expression lock, Statement body)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:syncronizedStatement(l, body), map[loc, set[loc]] env, FlowEnvironment fenv, rel[loc,loc] locks, set[Stmt] stmts){
	<stmts, potential, env, exs> = gatherStmtFromExpressions(m, l, env, locks, stmts);
	stmts = addAndLock(potential, locks, stmts);
	
	vlock = getDeclFromRead(getOneFrom(potential));	
	<stmts, env, fenv, exsC> = gatherStmtFromStatements(m, b, env, fenv, locks + {<s@src, vlock>}, stmts);
	exs = mergeExceptions(exs, exsC);
	return <stmts, env, fenv, exsC>;
}

//throw(Expression exp)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:\throw(exp), map[loc, set[loc]] env, FlowEnvironment fenv, rel[loc,loc] locks, set[Stmt] stmts){
	exs = (extractClassName(exp@decl) : env);
	return <stmts, env, fenv, exs>;
}

//\try(Statement body, list[Statement] catchClauses)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:\try(body, catchStatements), map[loc, set[loc]] env, FlowEnvironment fenv, rel[loc,loc] locks, set[Stmt] stmts){
	<stmts, env, fenv, exsInner> = gatherStmtFromStatements(m, body, env, fenv, locks, stmts);	
	exs = ();
	for(cs <- catchStatements){
		<stmts, env, fenv, exsC> = gatherStmtFromCatchStatements(m, cs, env, fenv, locks, exsInner, stmts);	
		exs = mergeExceptions(exs,exsC);
	}
	return <stmts, env, fenv, exs>;
}

//\try(Statement body, list[Statement] catchClauses, Statement \finally)  

//\catch(Declaration exception, Statement body)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[str, map[loc, set[loc]]]] gatherStmtFromCatchStatements(Declaration m, Statement s:\catch(except, body), map[loc, set[loc]] env, FlowEnvironment fenv, rel[loc,loc] locks, map[str, map[loc, set[loc]]] exs, set[Stmt] stmts){
	envCatch = ();
	exsCatch = ();
	visit(except){
		case e:simpleName(_) : {
			if(e@decl.path in exs){
				<stmts, envCatch, fenv, exsCatch> = gatherStmtFromStatements(m, body, updateEnvironment(env,exs[e@decl.path]), fenv, locks, stmts);
				envCatch = merge(envCatch,env);
			}
		}
	}
	return <stmts, env, fenv, exsCatch>;
}

//\declarationStatement(Declaration declaration)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:\declarationStatement(d), map[loc, set[loc]] env, FlowEnvironment fenv, rel[loc,loc] locks, set[Stmt] stmts){
	exs = ();
	top-down-break visit(d) {
		case Expression e : {
			<stmts, _, env, exsC> = gatherStmtFromExpressions(m, e, env, locks, stmts);
			exs = mergeExceptions(exs, exsC);
		}
		case Statement s : {
			<stmts, env, _, exsC> = gatherStmtFromStatements(m, s, env, fenv, locks, stmts);
			exs = mergeExceptions(exs, exsC);
		}
	}
	return <stmts, env, fenv, exs>;
}


//\while(Expression condition, Statement body)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:\while(cond, body), map[loc, set[loc]] env, FlowEnvironment fenv, rel[loc, loc] locks, set[Stmt] stmts){
	return dealWithLoopsConditionFirst(m, [], cond, [], body, env, fenv, locks, stmts);
}

//\expressionStatement(Expression stmt)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement s:expressionStatement(e), map[loc, set[loc]] env, FlowEnvironment fenv, rel[loc, loc] locks, set[Stmt] stmts){
	<stmts, _, env, exs> = gatherStmtFromExpressions(m, e, env, locks, stmts);
	return <stmts, env, fenv, exs>;
}

 //\constructorCall(bool isSuper, Expression expr, list[Expression] arguments)
 //\constructorCall(bool isSuper, list[Expression] arguments)



tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[str, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m, Statement b, map[loc, set[loc]] env, FlowEnvironment fenv, rel[loc, loc] locks, set[Stmt] stmts){
	println("case I do not need : <b>");
	return <stmts, env, fenv, ()>;
}