module lang::sccfg::ast::util::DataFlowGraph

import lang::sccfg::ast::DataFlowLanguage;
import lang::sccfg::converter::Java2DFG;

import IO;
import List;
import Relation;

public data GraphNode = access(loc address, loc variable)
						| lock(loc address, loc variable);
alias DFG = rel[GraphNode from, GraphNode to];

DFG buildGraph(Program p){
	DFG g = buildDataDependencies(p) + buildSynchronizedDependencies(p);
	return g + buildVolatileDependencies(p, g);
}
	 
DFG buildDataDependencies(Program p)
	// when the variable "from" is read and used in the write of "to"
	 = { <access(to,varTo), access(from, varFrom)> | assign(to, varTo, dependOn) <- p.statements, read(from, varFrom, _) <- p.statements, dependOn == from}
	 //when the variable "from" is the assignment read at stmt "to"
	 + { <access(to, varTo), access(from, varFrom)> | read(to, varTo, dependOn) <- p.statements, assign(from, varFrom, _) <- p.statements, dependOn == from}
	 //when the variable "from" is a read and depends on another read
	 + { <access(to, varTo), access(from, varFrom)> | read(to, varTo, dependOn) <- p.statements, read(from, varFrom, _) <- p.statements, dependOn == from}	
	;
	
DFG buildSynchronizedDependencies(Program p)
	 //acquire dependency from synchronized
	 = { <access(getIdFromStmt(stmt), getVarFromStmt(stmt)), GraphNode::lock(address, l)> | Stmt::lock(address, l, stmts) <- p.statements, stmt <- stmts}
	 //release dependency from synchronized
	 + { <GraphNode::lock(address, l), access(getIdFromStmt(stmt), getVarFromStmt(stmt))> | Stmt::lock(address, l, stmts) <- p.statements, stmt <- stmts}
	;
	
DFG buildVolatileDependencies(Program p, DFG g)
	//acquire dependency from volatile
	 = { <stmt, GraphNode::lock(address, volVar)> | attribute(volVar, true) <- p.decls, <stmt,access(address, varRead)> <- g, read(id, variable,_) <- p.statements, id == address, volVar == varRead}
	 //release dependency from volatile
	 + { <GraphNode::lock(address, volVar), stmt> | attribute(volVar, true) <- p.decls, <access(address, varAssign), stmt> <- g, assign(id, variable,_) <- p.statements, id == address, volVar == varAssign}
	 
	;
	