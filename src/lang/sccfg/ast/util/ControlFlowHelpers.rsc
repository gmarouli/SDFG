module lang::sccfg::ast::util::ControlFlowHelpers

import IO;
import lang::sccfg::ast::DataFlowLanguage;
import lang::sccfg::ast::Java2DFG;
import lang::java::m3::TypeSymbol;
import lang::java::jdt::m3::AST;

tuple[set[Stmt], map[loc,set[loc]], set[Stmt], map[loc,set[loc]], map[loc,set[loc]]] branching(Declaration m, Statement branch1, Statement branch2, map[loc,set[loc]] env){
	currentBlock = {};
	potentialStmt = {};
	map[loc,set[loc]] potentialContinueEnv = ();
	map[loc,set[loc]] potentialBreakEnv = ();
	<unnestedStmts,env, nestedReads, continueEnv, breakEnv> = dealWithStmts(m, branch1, env);
	currentBlock += unnestedStmts;
	potentialStmt += nestedReads;
	potentialContinueEnv = mergeInBlockEnvironments(continueEnv,potentialContinueEnv);
	potentialBreakEnv = mergeInBlockEnvironments(breakEnv,potentialBreakEnv);
				
	<unnestedStmts,envR, nestedReads, continueEnv, breakEnv> = dealWithStmts(m, branch2, env);
	currentBlock += unnestedStmts;
	potentialStmt += nestedReads;
	potentialContinueEnv = mergeInBlockEnvironments(continueEnv,potentialContinueEnv);
	potentialBreakEnv = mergeInBlockEnvironments(breakEnv,potentialBreakEnv);
	env = mergeEnvironments(env,envR);	
	return <currentBlock, env, potentialStmt,potentialContinueEnv,potentialBreakEnv>;
}

map[loc,set[loc]] mergeEnvironments(map[loc,set[loc]] env, map[loc,set[loc]] tempEnv){
	for(variable <- tempEnv){
		if(variable in env){
			env[variable] = env[variable] + tempEnv[variable];
		}
	}
	return env;
}

map[loc,set[loc]] mergeInBlockEnvironments(map[loc,set[loc]] env1, map[loc,set[loc]] env2){
	for(variable <- env2){
		if(variable in env1){
			env1[variable] = env1[variable] + env2[variable];
		}
		else{
			env1[variable] = env2[variable];
		}
	}
	return env1;
}