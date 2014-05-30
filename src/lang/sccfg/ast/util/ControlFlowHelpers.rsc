module lang::sccfg::ast::util::ControlFlowHelpers

import IO;
import lang::sccfg::ast::DataFlowLanguage;
import lang::sccfg::ast::util::EnvironmentManagement;
import lang::sccfg::ast::Java2DFG;
import lang::java::m3::TypeSymbol;
import lang::java::jdt::m3::AST;

tuple[set[Stmt], set[Stmt], Environment] branching(Declaration m, Statement branch1, Statement branch2, Environment env){
	currentBlock = {};
	potentialStmt = {};

	<unnestedStmts, nestedReads, env> = dealWithStmts(m, branch1, env);
	currentBlock += unnestedStmts;
	potentialStmt += nestedReads;
				
	<unnestedStmts, nestedReads, envR> = dealWithStmts(m, branch2, env);
	currentBlock += unnestedStmts;
	potentialStmt += nestedReads;
	env = mergeEnvironments(env,envR);
	return <currentBlock, potentialStmt, env>;
}

tuple[set[Stmt], set[Stmt], Environment] dealWithLoopsConditionFirst(Declaration m, list[Expression] initializers, Expression cond, list[Expression] updaters, Statement stmts, Environment env){
	currentBlock = {};
	potentialStmt = {};
	previousHelpingEnvironment = env;
	<unnestedStmts, nestedReads, env> = dealWithStmts(m, \block([\expressionStatement(i) | i <- initializers]), environment(getCurrentEnvironment(env),(),(),getReturnEnvironment(env)));
	currentBlock += unnestedStmts;
	
	//running the condition after one loop getting all the connections from statements and continue command
	<unnestedStmts, nestedReads, env> = dealWithStmts(m, \expressionStatement(cond), env);
	currentBlock += unnestedStmts + nestedReads;

	//executed once all the reads and assigns added missing connections to itself
	<unnestedStmts, nestedReads, loopedEnv> = dealWithStmts(m, stmts, env);
	currentBlock += unnestedStmts;
	
	//include continue
	loopedEnv = mergeContinue(loopedEnv);
	
	//running the condition after one loop getting all the connections from statements and continue command
	<unnestedStmts, nestedReads, loopedEnv> = dealWithStmts(m, \block([\expressionStatement(u) | u <- updaters]), loopedEnv);
	currentBlock += unnestedStmts;

	//running the condition after one loop getting all the connections from statements and continue command
	<unnestedStmts, nestedReads, exitEnv> = dealWithStmts(m, \expressionStatement(cond), loopedEnv);
	currentBlock += unnestedStmts + nestedReads;

	<unnestedStmts, n, loopedEnv> = dealWithStmts(m, stmts, exitEnv);
	currentBlock += unnestedStmts;
	
	exitEnv = mergeBreak(exitEnv);
	
	env = mergeEnvironments(env,exitEnv);
	env = resetHelpingEnvironment(env,previousHelpingEnvironment);
	
	return <currentBlock, potentialStmt, env>;
}
