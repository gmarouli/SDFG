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

