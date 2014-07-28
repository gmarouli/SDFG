module lang::sdfg::converter::util::Getters

import Set;
import String;

import lang::java::jdt::m3::AST;
import lang::java::m3::TypeSymbol;

import lang::sdfg::ast::SynchronizedDataFlowGraphLanguage;

//Getters
loc getIdFromStmt(Stmt::read(id, _, _)) = id;
loc getIdFromStmt(Stmt::assign(id, _, _)) = id;
loc getIdFromStmt(Stmt::change(id, _, _)) = id;
loc getIdFromStmt(Stmt::acquireLock(id, _, _)) = id;
loc getIdFromStmt(Stmt::releaseLock(id, _, _)) = id;
loc getIdFromStmt(Stmt::create(id, _, _)) = id;
loc getIdFromStmt(Stmt::call(id, _, _, _)) = id;
loc getIdFromStmt(Stmt::entryPoint(id, _)) = id;
loc getIdFromStmt(Stmt::exitPoint(id, _)) = id;

loc getVarFromStmt(Stmt::read(_, var, _)) = var;
loc getVarFromStmt(Stmt::assign(_, var, _)) = var;
loc getVarFromStmt(Stmt::change(_, var, _)) = var;
loc getVarFromStmt(Stmt::acquireLock(_, var, _)) = var;
loc getVarFromStmt(Stmt::releaseLock(_, var, _)) = var;
loc getVarFromStmt(Stmt::create(_, var, _)) = var;
loc getVarFromStmt(Stmt::call(_, var, _, _)) = var;
loc getVarFromStmt(Stmt::entryPoint(_, var)) = var;
loc getVarFromStmt(Stmt::exitPoint(_, var)) = var;

loc getDependencyFromStmt(Stmt::read(_, _, d)) = d;
loc getDependencyFromStmt(Stmt::assign(_, _, r)) = r;
loc getDependencyFromStmt(Stmt::change(_, _, d)) = d;
loc getDependencyFromStmt(Stmt::acquireLock(_, _, s)) = s;
loc getDependencyFromStmt(Stmt::releaseLock(_, _, s)) = s;
loc getDependencyFromStmt(Stmt::create(_, _, p)) = p;
loc getDependencyFromStmt(Stmt::call(_, _, _, p)) = p;
//the (1,1) is needed to exclude it from the new ids
loc getDependencyFromStmt(Stmt::entryPoint(_, _)) = emptyId(1,1);
loc getDependencyFromStmt(Stmt::exitPoint(_, _)) = emptyId(1,1);

loc getDeclFromRead(Stmt::read(_,decl,_)) = decl;


set[loc] gatherValues(list[Expression] es)
	= union({gatherValues(e) | e <- es});
set[loc] gatherValues(Expression e:conditional(cond,ifB,elseB))
	= gatherValues(cond) + gatherValues(ifB) + gatherValues(elseB);
set[loc] gatherValues(Expression e:arrayInitializer(elements))
	= gatherValues(elements);
set[loc] gatherValues(Expression e:null())
	= {independentValue + "null"};
set[loc] gatherValues(Expression e:number(n))
	= {independentValue + n};
set[loc] gatherValues(Expression e:booleanLiteral(b)){
	if(b)
		return {independentValue + "true"};
	else
		return {independentValue + "false"};
}
set[loc] gatherValues(Expression e:stringLiteral(s))
	= {independentValue + s};
set[loc] gatherValues(Expression e:infix(lhs, _, rhs, exts))
	= gatherValues(lhs) + gatherValues(rhs) + gatherValues(exts);
set[loc] gatherValues(Expression e:prefix(_, operand))
	= gatherValues(operand);
set[loc] gatherValues(Expression e:postfix(operand,_))
	= gatherValues(operand);
default set[loc] gatherValues(Expression e)
	= {};
	

set[Stmt] getSynchronizationActions(Program p)
	= {s | s <- p.statements, isSyncDependency(s)};
	
str extractClassName(loc method) 
	= substring(method.path,0,findLast(method.path,"/"));
	
set[loc] getDataDependencyIds(set[Stmt] potential)
	= { id | Stmt::read(id, _, _) <- potential}
	+ { id | Stmt::call(id, _, _) <- potential}
	+ { id | Stmt::create(id, _, _) <- potential}
	;	

loc getTypeDeclFromTypeSymbol(TypeSymbol c:class(decl, []))
	= decl;
//loc getTypeDeclFromTypeSymbol(TypeSymbol i:\int())
//	= |java+primitive:///int|;
//loc getTypeDeclFromTypeSymbol(TypeSymbol b:boolean())
//	= |java+primitive:///boolean|;
loc getTypeDeclFromTypeSymbol(TypeSymbol c:class(decl, [x])){
	decl.path = decl.path + "\<" + getTypeDeclFromTypeSymbol(x).path +"\>";
	return decl;
}
loc getTypeDeclFromTypeSymbol(TypeSymbol c:interface(decl, [x])){
	decl.path = decl.path + "\<" + getTypeDeclFromTypeSymbol(x).path +"\>";
	return decl;
}
loc getTypeDeclFromTypeSymbol(TypeSymbol t:\array(TypeSymbol component, int dimension)){
	loc decl = |java+array:///|;
	decl.path = getTypeDeclFromTypeSymbol(component).path + "[<dimension>]";
	return decl;
}
default loc getTypeDeclFromTypeSymbol(TypeSymbol c){
	if(TypeSymbol::boolean() := c)
		return |java+array:///boolean|;
	else if(TypeSymbol::\int() := c)
		return |java+array:///int|;
	assert false : "Unknown type symbol <c>";
}
	
//Predicates
bool isDataAccess(Stmt s:acquireLock(_,_,_)) = false;
bool isDataAccess(Stmt s:releaseLock(_,_,_)) = false;
bool isDataAccess(Stmt s:entryPoint(_,_)) = false;
bool isDataAccess(Stmt s:exitPoint(_,_)) = false;
default bool isDataAccess(Stmt s) = true;

bool isSyncDependency(Stmt s:acquireLock(_,_,_)) = true;
bool isSyncDependency(Stmt s:releaseLock(_,_,_)) = true;
default bool isDataAccess(Stmt s) = true;

bool isClass(TypeSymbol c:class(_,_))
	= true;
default bool isClass(TypeSymbol c)
	= false;
	
bool isField(loc decl) = decl.scheme == "java+field";