module lang::sccfg::ast::util::DataFlowGraph

import lang::sccfg::ast::DataFlowLanguage;

import IO;
import List;
import Relation;

public data GraphNode = graphNode(loc var, loc address); 
alias DFG = rel[GraphNode from, GraphNode to];

DFG buildGraph(Program p)
	// when the variable "from" is read and used in the write of "to"
	 = { <graphNode(to, id1), graphNode(from, id2)> | assign(id1, to, dependOn) <- p.statements, read(id2, from, _) <- p.statements, dependOn == id2}
	 + { <graphNode(to, id1), graphNode(from, id2)> | read(id1, to, dependOn) <- p.statements, assign(id2, from, _) <- p.statements, dependOn == id2}
	;