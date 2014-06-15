module lang::sccfg::converter::util::ControlFlowHelpers

import IO;
import lang::sccfg::ast::DataFlowLanguage;
import lang::sccfg::converter::util::EnvironmentManagement;
import lang::sccfg::converter::Java2DFG;
import lang::java::m3::TypeSymbol;
import lang::java::jdt::m3::AST;
import lang::sccfg::converter::GatherStmtFromStatements;
import lang::sccfg::converter::GatherStmtFromExpressions;

tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[str, map[loc, set[loc]]]] branching(Declaration m, Statement ifBranch, Statement elseBranch, map[loc, set[loc]] env, lrel[loc, loc] locks, set[Stmt] stmts){

	<stmts, envIf, fenvIf, exsIf> = gatherStmtFromStatements(m, ifBranch, env, locks, stmts);				
	<stmts, envElse, fenvElse, exsElse> = gatherStmtFromStatements(m, elseBranch, env, locks, stmts);

	env = updateEnvironment(env,envIf);
	env = mergeNestedEnvironment(env,envElse);
	return <stmts, env, mergeFlow(fenvIf, fenvElse), mergeExceptions(exsIf, exsElse)>;
}

tuple[set[Stmt], set[Stmt], map[loc, set[loc]], map[str, map[loc, set[loc]]]] shortCircuit(Declaration m, Expression ifBranch, Expression elseBranch, map[loc, set[loc]] env, lrel[loc, loc] locks, set[Stmt] stmts){

	<stmts, potential, envComp, exsComp> = gatherStmtFromExpressions(m, ifBranch, env, locks, stmts);
				
	<stmts, potentialOpt, envOpt, exsOpt> = gatherStmtFromExpressions(m, elseBranch, envComp, locks, stmts);

	env = updateEnvironment(env, envComp);
	env = mergeNestedEnvironment(env,envOpt);
	return <stmts, potential + potentialOpt, env, mergeExceptions(exsComp, exsOpt)>;
}


tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[str, map[loc, set[loc]]]] dealWithLoopsConditionFirst(Declaration m, list[Expression] initializers, Expression cond, list[Expression] updaters, Statement body, map[loc, set[loc]] env, lrel[loc, loc] locks, set[loc] stmts){
	outerEnv = env;
	exs = ();
	for(i <- initializers){
		<stmts, _, env, exsC> = gatherStmtFromExpressions(m, i, env, locks, stmts);
		exs = mergeExceptions(exs, exsC);
	}
	
	<stmts, potential, env, exsC> = gatherStmtFromExpressions(m, cond, env, locks, stmts);
	exs = mergeExceptions(exs, exsC);
	stmts = addAndLock(potential, locks, stmts);
	
	outerEnv = updateEnvironment(outerEnv, env);
	
	<stmts, env, fenvInner, exsC> = gatherStmtFromStatements(m, body, env, locks, stmts);
	exs = mergeExceptions(exs, exsC);
	env = mergeNestedEnvironment(env, getContinueEnvironment(fenvInner));
	
	for(u <- updaters){
		<stmts, _, env, exsC> = gatherStmtFromExpressions(m, u, env, locks, stmts);
		exs = mergeExceptions(exs, exsC);
	}
	
	<stmts, potential, env, _> = gatherStmtFromExpressions(m, cond, env, locks, stmts);
	stmts = addAndLock(potential, locks, stmts);
	
	<stmts, _, fenvInner, _> = gatherStmtFromStatements(m, body, env, locks, stmts);
	env = mergeNestedEnvironment(env, getBreakEnvironment(fenvInner));
	
	return <stmts, mergeNestedEnvironment(outerEnv, env), emptyFlowEnvironment(), exs>;
}