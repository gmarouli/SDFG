module lang::sccfg::converter::util::ControlFlowHelpers

import IO;
import lang::sccfg::ast::DataFlowLanguage;
import lang::sccfg::converter::util::EnvironmentManagement;
import lang::java::m3::TypeSymbol;
import lang::java::jdt::m3::AST;
import lang::sccfg::converter::GatherStmtFromStatements;
import lang::sccfg::converter::GatherStmtFromExpressions;

tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc], map[str, map[loc, set[loc]]]] branching(Declaration m, Statement ifBranch, Statement elseBranch, map[loc, set[loc]] env, set[loc] volatileFields, rel[loc, loc] acquireActions, set[Stmt] stmts){
	outeracquireActions = acquireActions;
	<stmts, envIf, fenvIf, acquireActionsIf, exsIf> = gatherStmtFromStatements(m, ifBranch, env, volatileFields, outerAcquireActions, stmts);				
	acquireActions += acquireActionsIf;
	<stmts, envElse, fenvElse, acquireActionsElse, exsElse> = gatherStmtFromStatements(m, elseBranch, env, volatileFields, outerAcquireActions, stmts);
	acquireActions += acquireActionsElse;
	env = updateEnvironment(env,envIf);
	env = mergeNestedEnvironment(env,envElse);
	return <stmts, env, mergeFlow(fenvIf, fenvElse), acquireActions, mergeExceptions(exsIf, exsElse)>;
}

tuple[set[Stmt], set[Stmt], map[loc, set[loc]], rel[loc,loc], map[str, map[loc, set[loc]]]] shortCircuit(Declaration m, list[Expression] e:[exp, *exps], map[loc, set[loc]] env, set[loc] volatileFields, rel[loc, loc] acquireActions, set[Stmt] stmts){
	<stmts, potential, env, acquireActions, exs> = gatherStmtFromExpressions(m, exp, env, volatileFields, acquireActions, stmts);
	stmts += potential;
	acquireActions += extractAcquireActions(potential, volatileFields);
	
	envOp = env;
	for(expRest <- exps){
		<stmts, potentialOp, envOp, exsOp> = gatherStmtFromExpressions(m, expRest, envOp, locks, stmts);
		stmts += potentialOp;
		acquireActions += extractAcquireActions(potentialOp, volatileFields);
		env = mergeNestedEnvironment(env,envOp);
		exs = mergeExceptions(exs, exsOp);
		potential += potentialOp;
	}			
	return <stmts, potential, env, acquireActions, exs>;
}


tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, rel[loc,loc], map[str, map[loc, set[loc]]]] dealWithLoopsConditionFirst(Declaration m, list[Expression] initializers, Expression cond, list[Expression] updaters, Statement body, map[loc, set[loc]] env, set[loc] volatileFields, rel[loc, loc] acquireActions, set[Stmt] stmts){
	outerEnv = env;
	exs = ();
	for(i <- initializers){
		<stmts, _, env, acquireActions, exsC> = gatherStmtFromExpressions(m, i, env, volatileFields, acquireActions, stmts);
		exs = mergeExceptions(exs, exsC);
	}
	
	<stmts, potential, env, acquireActions, exsC> = gatherStmtFromExpressions(m, cond, env, volatileFields, acquireActions, stmts);
	stmts += potential;
	acquireActions += extractAcquireActions(potential, volatileFields);
	exs = mergeExceptions(exs, exsC);
	
	outerEnv = updateEnvironment(outerEnv, env);
	
	<stmts, env, fenvInner, acquireActions, exsC> = gatherStmtFromStatements(m, body, env, volatileFields, acquireActions, stmts);
	exs = mergeExceptions(exs, exsC);
	env = mergeNestedEnvironment(env, getContinueEnvironment(fenvInner));
	
	for(u <- updaters){
		<stmts, _, env, acquireActions, exsC> = gatherStmtFromExpressions(m, u, env, volatileFields, acquireActions, stmts);
		exs = mergeExceptions(exs, exsC);
	}
	
	<stmts, potential, env, _, _> = gatherStmtFromExpressions(m, cond, env, volatileFields, acquireActions, stmts);
	stmts += potential;
	
	<stmts, _, fenvInner, _, _> = gatherStmtFromStatements(m, body, env, volatileFields, acquireActions, stmts);
	env = mergeNestedEnvironment(env, getBreakEnvironment(fenvInner));
	
	return <stmts, mergeNestedEnvironment(outerEnv, env), emptyFlowEnvironment(), acquireActions, exs>;
}