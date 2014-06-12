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

//assert(Expression expression)
//assert(Expression expression, Expression message)

//block(list[Statement] statements)
tuple[set[Stmt], map[loc,set[loc]], FlowEnvironment, map[loc, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m , Statement s:\block(sB), map[loc, set[loc]] env, FlowEnvironment fenv, map[loc, map[loc, set[loc]]] exs, set[Stmt] stmts){
	envInner = env;
	for(stmt <- sB){
		<stmts, envInner, fenv, exs> = gatherStmtFromStatements(m, stmt, envInner, fenv, exs, stmts);
	}
	env = updateEnvironment(env, envInner);
	return <stmts, env, fenv, exs>;
}

//break()
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[loc, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m , Statement s:\break(), map[loc, set[loc]] env, FlowEnvironment fenv, map[loc, map[loc, set[loc]]] exs, set[Stmt] stmts){
	return <stmts, env, mergeBreak(fenv, env), exs>;
}

//break("")
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[loc, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m , Statement s:\break(""), map[loc, set[loc]] env, FlowEnvironment fenv, map[loc, map[loc, set[loc]]] exs, set[Stmt] stmts){
	// ISSUE: what if break is not in a branch? then it is perceived partly as a continue
	return <stmts, env, mergeBreak(fenv, env), exs>;
}

//break(str label)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[loc, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m , Statement s:\break(_), map[loc, set[loc]] env, FlowEnvironment fenv, map[loc, map[loc, set[loc]]] exs, set[Stmt] stmts){
	assert false : "Labeled statement (break) found!!!";
	return <stmts, env, fenv, exs>;
}

//continue()
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[loc, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m , Statement s:\continue(), map[loc, set[loc]] env, FlowEnvironment fenv, map[loc, map[loc, set[loc]]] exs, set[Stmt] stmts){
	return <stmts, env, mergeContinue(fenv, env), exs>;
}

//continue(str label)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[loc, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m , Statement s:\continue(_), map[loc, set[loc]] env, FlowEnvironment fenv, map[loc, map[loc, set[loc]]] exs, set[Stmt] stmts){
	assert false : "Labeled statement (continue) found!!!";
	return <stmts, env, fenv, exs>;
}

//do(Statement body, Expression condition)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[loc, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m , Statement s:\do(b, cond), map[loc, set[loc]] env, FlowEnvironment fenv, map[loc, map[loc, set[loc]]] exs, set[Stmt] stmts){
		
	//executed once all the reads and assigns added missing connections to itself
	<stmts, env, fenvInner, exs> = gatherStmtFromStatements(m, b, env, flowEnvironment((),()), exs, stmts);
			
	//include continue
	env = mergeNestedEnvironment(env, getContinueEnvironment(fenvInner));
			
	//running the condition after one loop getting all the connections from statements and continue command
	<stmts, potential, env, exs> = gatherStmtFromExpressions(m, cond, env, exs, stmts);
	stmts += potential;
	
	//connect the statements with the condition but the environment and exception are already found
	<stmts, env, fenv, exs> = gatherStmtFromStatements(m, b, env, fenvInner, exs, stmts);

	env = mergeNestedEnvironment(env, getBreakEnvironment(fenvInner));
	
	return <stmts, env, fenv, exs>;
}

//foreach(Declaration parameter, Expression collection, Statement body)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[loc, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m , Statement s:\foreach(parameter, collection, body), map[loc, set[loc]] env, FlowEnvironment fenv, map[loc, map[loc, set[loc]]] exs, set[Stmt] stmts){
	outerEnv = env;
	<stmts, potential, env, exs> = gatherStmtFromExpressions(m, collection, env, exs, stmts);
	stmts += potential;
	stmts += { Stmt::assign(s@src, parameter@decl, s@src)};
	env[parameter@decl] = {s@src};
	
	outerEnv = updateEnvironment(outerEnv, env);
	
	//executed once all the reads and assigns added missing connections to itself
	<stmts, env, fenvInner, exs> = gatherStmtFromStatements(m, b, env, flowEnvironment((),()), exs, stmts);
			
	//include continue
	env = mergeNestedEnvironment(env, getContinueEnvironment(fenvInner));
			
	//running the condition after one loop getting all the connections from statements and continue command
	<stmts, potential, env, exs> = gatherStmtFromExpressions(m, collection, env, exs, stmts);
	stmts += potential;
	
	//connect the statements with the condition but the environment and exception are already found
	<stmts, env, fenv, exs> = gatherStmtFromStatements(m, b, env, fenvInner, exs, stmts);

	env = mergeNestedEnvironment(env, getBreakEnvironment(fenvInner));
	
	return <stmts, mergeNestedEnvironment(outerEnv,env), fenv, exs>;
}

//for(list[Expression] initializers, Expression condition, list[Expression] updaters, Statement body)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[loc, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m , Statement s:\for(initializers, cond, updaters, body), map[loc, set[loc]] env, FlowEnvironment fenv, map[loc, map[loc, set[loc]]] exs, set[Stmt] stmts){
	return dealWithLoopsConditionFirst(m, initializers, cond, updaters, body, env, fenv, exs, stmts);
} 

//for(list[Expression] initializers, list[Expression] updaters, Statement body)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[loc, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m , Statement s:\for(initializers, updaters, body), map[loc, set[loc]] env, FlowEnvironment fenv, map[loc, map[loc, set[loc]]] exs, set[Stmt] stmts){
	return dealWithLoopsConditionFirst(m, initializers, Expression::\null(), updaters, body, env, fenv, exs, stmts);
}

//expressionStatement(Expression stmt)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[loc, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m , Statement s:\expressionStatement(e), map[loc, set[loc]] env, FlowEnvironment fenv, map[loc, map[loc, set[loc]]] exs, set[Stmt] stmts){
	<stmts, potential, env, exs> = gatherStmtFromExpressions(m, e, env, exs, stmts);
	return <stmts, env, fenv, exs>;
}

//if(Expression condition, Statement thenB)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[loc, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m , Statement s:\if(cond, thenB), map[loc, set[loc]] env, FlowEnvironment fenv, map[loc, map[loc, set[loc]]] exs, set[Stmt] stmts){
	<stmts, potential, env, exs> = gatherStmtFromExpressions(m, cond, env, exs, stmts);
	stmts += potential;
	
	<stmts, envOpt, fenv, exs> = gatherStmtFromStatements(m, thenB, env, fenv, exs, stmts);			

	env = mergeNestedEnvironment(env,envOpt);
	return <stmts, env, fenv, exs>;
}

//if(Expression condition, Statement thenB, Statement elseB)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[loc, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m , Statement s:\if(cond, thenB, elseB), map[loc, set[loc]] env, FlowEnvironment fenv, map[loc, map[loc, set[loc]]] exs, set[Stmt] stmts){
	<stmts, potential, env, exs> = gatherStmtFromExpressions(m, cond, env, exs, stmts);
	stmts += potential;
	
	return branching(m, thenB, elseB, env, fenv, exs, stmts);
}

//label(str name, Statement body)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[loc, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m , Statement s:\label(_, _), map[loc, set[loc]] env, FlowEnvironment fenv, map[loc, map[loc, set[loc]]] exs, set[Stmt] stmts){
	assert false: "Labeled block";
	return <stmts, env, fenv, exs>;
}

//return(Expression expression)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[loc, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m , Statement s:\return(exp), map[loc, set[loc]] env, FlowEnvironment fenv, map[loc, map[loc, set[loc]]] exs, set[Stmt] stmts){
	<stmts, potential, env, exs> = gatherStmtFromExpressions(m, exp, env, exs, stmts);
	stmts += potential;
	return <stmts, env, fenv, exs>;
}

//return()
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[loc, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m , Statement s:\return(), map[loc, set[loc]] env, FlowEnvironment fenv, map[loc, map[loc, set[loc]]] exs, set[Stmt] stmts){
	return <stmts, env, fenv, exs>;
}

//switch(Expression exp, list[Statement] statements)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[loc, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m , Statement s:\switch(exp, body), map[loc, set[loc]] env, FlowEnvironment fenv, map[loc, map[loc, set[loc]]] exs, set[Stmt] stmts){
	<stmts, potential, env, exs> = gatherStmtFromExpressions(m, exp, env, exs, stmts);
	stmts += potential;
	
	outerEnv = env;
	exitEnv = ();
	fenvInner = flowEnvironment((),());
	
	list[Statement] currentCase = [];
	hasDefault = false;
	for(stmt <- body){
		switch(stmt){
			case \case(_):{
				<stmts, currentEnv, env, fenvInner> = gatherStmtFromStatements(m, \block(currentCase), currentEnv, fenvInner, exs, stmts);
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
				<stmts, currentEnv, fenvInner, exs> = gatherStmtFromStatements(m, \block(currentCase), currentEnv, fenvInner, exs, stmts);
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

	<stmts, currentEnv, fenvInner, exs> = gatherStmtFromStatements(m, \block(currentCase), currentEnv, fenv, exs, stmts);	
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
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[loc, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m , Statement s:syncronizedStatement(l, body), map[loc, set[loc]] env, FlowEnvironment fenv, map[loc, map[loc, set[loc]]] exs, set[Stmt] stmts){
	<stmts, potential, env, exs> = gatherStmtFromExpressions(m, l, env, exs, stmts);
	stmts += potential;
	vlock = getDeclFromRead(getOneFrom(potential));	
	
	oldStmts = stmts;
	<stmts, env, fenv, exs> = gatherStmtFromStatements(m, b, env, fenv, exs, stmts);
	
	// TODO needs to be fixed!!! It is going to be too slow
	stmts += {Stmt::lock(s@src, vlock, {lockedStmt | lockedStmt <- (stmts - oldStmts)})};
	return <stmts, env, fenv, exs>;
}

//throw(Expression exp)
tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[loc, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m , Statement s:\throw(exp), map[loc, set[loc]] env, FlowEnvironment fenv, map[loc, map[loc, set[loc]]] exs, set[Stmt] stmts){
	//println(getType(exp@typ));
	return <stmts, env, fenv, exs>;
}

tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[loc, map[loc, set[loc]]]] gatherStmtFromStatements(Declaration m , Statement b, map[loc, set[loc]] env, FlowEnvironment fenv, map[loc, map[loc, set[loc]]] exs, set[Stmt] stmts){
	println("in stttms failing : <b>");
	return <stmts, env, fenv, exs>;
}