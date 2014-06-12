module lang::sccfg::converter::util::ControlFlowHelpers

import IO;
import lang::sccfg::ast::DataFlowLanguage;
import lang::sccfg::converter::util::EnvironmentManagement;
import lang::sccfg::converter::Java2DFG;
import lang::java::m3::TypeSymbol;
import lang::java::jdt::m3::AST;
import lang::sccfg::converter::GatherStmtFromStatements;
import lang::sccfg::converter::GatherStmtFromExpressions;

tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[loc, map[loc, set[loc]]]] branching(Declaration m, Statement ifBranch, Statement elseBranch, map[loc, set[loc]] env, FlowEnvironment fenv, map[loc, map[loc, set[loc]]] exs, set[Stmt] stmts){

	<stmts, envIf, fenv, exs> = gatherStmtFromStatements(m, ifBranch, env, fenv, exs, stmts);				
	<stmts, envElse, fenv, exs> = gatherStmtFromStatements(m, elseBranch, env, fenv, exs, stmts);

	env = updateEnvironment(env,envIf);
	env = mergeNestedEnvironment(env,envElse);
	return <stmts, env, fenv, exs>;
}

tuple[set[Stmt], set[Stmt], map[loc, set[loc]], map[loc, map[loc, set[loc]]]] shortCircuit(Declaration m, Expression ifBranch, Expression elseBranch, map[loc, set[loc]] env, map[loc, map[loc, set[loc]]] exs, set[Stmt] stmts){

	<stmts, potential, envComp, exs> = gatherStmtFromExpressions(m, ifBranch, env, exs, stmts);
				
	<stmts, potentialOpt, envOpt, exs> = gatherStmtFromExpressions(m, elseBranch, envComp, exs, stmts);

	env = updateEnvironment(env, envComp);
	env = mergeNestedEnvironment(env,envOpt);
	return <stmts, potential + potentialOpt, env, exs>;
}


tuple[set[Stmt], map[loc, set[loc]], FlowEnvironment, map[loc, map[loc, set[loc]]]] dealWithLoopsConditionFirst(Declaration m, list[Expression] initializers, Expression cond, list[Expression] updaters, Statement body, map[loc, set[loc]] env, FlowEnvironment fenv, map[loc, map[loc, set[loc]]] exs, set[loc] stmts){
	outerEnv = env;
	for(i <- initializers){
		<stmts, _, env, exs> = gatherStmtFromExpressions(m, i, env, exs, stmts);
	}
	
	<stmts, potential, env, exs> = gatherStmtFromExpressions(m, cond, env, exs, stmts);
	stmts += potential;
	
	outerEnv = updateEnvironment(outerEnv, env);
	
	<stmts, env, fenvInner, exs> = gatherStmtFromStatements(m, body, env, flowEnvironment((),()), exs, stmts);
	env = mergeNestedEnvironment(env, getContinueEnvironment(fenvInner));
	
	for(u <- updaters){
		<stmts, _, env, exs> = gatherStmtFromExpressions(m, u, env, exs, stmts);
	}
	
	<stmts, potential, env, exs> = gatherStmtFromExpressions(m, cond, env, exs, stmts);
	stmts += potential;
	
	<stmts, _, fenvInner, exs> = gatherStmtFromStatements(m, body, env, flowEnvironment((),()), exs, stmts);
	env = mergeNestedEnvironment(env, getBreakEnvironment(fenvInner));
	
	return <stmts, mergeNestedEnvironment(outerEnv, env), fenv, stmts>;
}