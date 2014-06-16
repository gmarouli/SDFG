module lang::sccfg::converter::util::DataFlowGraph

import lang::sccfg::ast::DataFlowLanguage;
import lang::sccfg::converter::Java2DFG;

import IO;
import List;
import Set;
import Relation;

public data GraphNode = access(loc address)
						| lock(loc address, loc variable);
alias DFG = rel[GraphNode from, GraphNode to];

DFG buildGraph(Program p) 
	= buildDataDependencies(p) 
	+ buildSynchronizedDependencies(p)
//	+ buildVolatileDependencies(p, g)
	;

	 
DFG buildDataDependencies(Program p)
	 = { <access(getIdFromStmt(stmt)), access(getDependencyFromStmt(stmt))> | stmt <- p.statements, isDataAccess(stmt)}
	;
	
DFG buildSynchronizedDependencies(Program p)
	 //acquire and release dependencies from synchronized
	 = union({ {<access(stmt), GraphNode::lock(address, l)>, <GraphNode::lock(address, l), access(stmt)>} | Stmt::lock(address, l, stmt) <- p.statements})
	;
	
//DFG buildVolatileDependencies(Program p, DFG g)
//	//acquire dependency from volatile
//	 = { <stmt, GraphNode::lock(address, volVar)> | attribute(volVar, true) <- p.decls, <stmt,access(address, varRead)> <- g, read(id, variable,_) <- p.statements, id == address, volVar == varRead}
//	 //release dependency from volatile
//	 + { <GraphNode::lock(address, volVar), stmt> | attribute(volVar, true) <- p.decls, <access(address, varAssign), stmt> <- g, assign(id, variable,_) <- p.statements, id == address, volVar == varAssign}
//	 
//	;
		
bool isDataAccess(Stmt s:lock(_,_,_)) = false;
default bool isDataAccess(Stmt s) = true;
