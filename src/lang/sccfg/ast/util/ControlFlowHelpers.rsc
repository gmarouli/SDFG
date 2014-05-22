module lang::sccfg::ast::util::ControlFlowHelpers

import lang::sccfg::ast::DataFlowLanguage;
import lang::java::m3::TypeSymbol;
import lang::java::jdt::m3::AST;

tuple[set[Stmt], map[loc,set[loc]], set[Stmt]] branching(Statement lhs, Statement rhs, map[loc,set[loc]] env){
	currentBlock = {};
	potentialStmt = {};
	<unnestedStmts,env, nestedReads> = dealWithStmts(m, \expressionStatement(lhs), env);
	currentBlock += unnestedStmts;
	potentialStmt += nestedReads;
				
	<unnestedStmts,envR, nestedReads> = dealWithStmts(m, \expressionStatement(rhs), env);
	currentBlock += unnestedStmts;
	potentialStmt += nestedReads;
	for(variable <- envR){
		if(variable in env){
			env[variable] = env[variable] + envR[variable];
		}
	}
	return <currentBlock, env, potentialStmt>;
}