module lang::sccfg::converter::util::DataFlowGraph

import lang::sccfg::ast::DataFlowLanguage;
import lang::sccfg::converter::util::Getters;
import IO;
import List;
import Set;
import Relation;

public data GraphNode = access(loc address)
					  | lock(loc address, loc variable);
alias DFG = rel[GraphNode from, GraphNode to];

DFG buildGraph(set[Stmt] stmts) 
	= buildDataDependencies(stmts) 
	+ buildSynchronizedDependencies(stmts)
	;

	 
DFG buildDataDependencies(set[Stmt] stmts)
	//missing connection call with receiver
	 = { <access(getIdFromStmt(stmt)), access(getDependencyFromStmt(stmt))> | stmt <- stmts, isDataAccess(stmt)}
	;
	
DFG buildSynchronizedDependencies(set[Stmt] stmts)
	 //acquire and release dependencies from synchronized
	 = {<access(stmt), GraphNode::lock(address, l)> | releaseLock(address, l, stmt) <- stmts}
	 + {<GraphNode::lock(address, l), access(stmt)> | acquireLock(address, l, stmt) <- stmts}
	;