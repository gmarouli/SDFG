module lang::sccfg::ast::util::ControlFlowHelpers

import IO;
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
	env = mergeEnvironments(env,envR);	
	return <currentBlock, env, potentialStmt>;
}

map[loc,set[loc]] mergeEnvironments(map[loc,set[loc]] env, map[loc,set[loc]] tempEnv){
	for(variable <- tempEnv){
		if(variable in env){
			env[variable] = env[variable] + tempEnv[variable];
		}
	}
	return env;
}

//tuple[list[int],list[int]] findContinueAndBreakOffset(Statement b){
//	firstCharacterOfContinue = [];
//	firstCharacterOfBreak = [];
//	top-down-break visit(b){
//		case c:\for(_,_,_) => c
//		case c:\for(_,_,_,_) => c
//		case c:\foreach(_,_,_) => c
//		case c:\while(_,_) => c
//		case c:\do(_,_) => c
//		case c:Statement::\continue(): {
//			firstCharacterOfContinue += c@src.offset;
//		}
//		case c:Statement::\break(""): {
//			firstCharacterOfBreak += c@src.offset;
//		}
//	}
//	return <firstCharacterOfContinue,firstCharacterOfBreak>;
//}

//tuple[map[loc,set[loc]], map[loc,set[loc]]] dealWithContinueAndBreak(set[Stmt] stmts, list[int] continueOffset, list[int] breakOffset){
//	continuedEnvs = (offset : () | offset <- continueOffset);
//	breakEnvs = (offset : () | offset <- breakOffset);
//	
//	for( Stmt::assign(src, decl, _) <- stmts){
//		if(src.offset < 
//	}
//	
//	return <continuedEnv, breakEnv>;
//}
