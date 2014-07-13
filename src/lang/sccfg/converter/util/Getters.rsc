module lang::sccfg::converter::util::Getters

import String;
import Set;

import lang::java::m3::TypeSymbol;
import lang::java::jdt::m3::AST;

import lang::sccfg::ast::DataFlowLanguage;

set[loc] gatherValues(list[Expression] es)
	= union({gatherValues(e) | e <- es});

set[loc] gatherValues(Expression e:conditional(cond,ifB,elseB))
	= gatherValues(cond) + gatherValues(ifB) + gatherValues(elseB);
set[loc] gatherValues(Expression e:arrayInitializer(elements))
	= gatherValues(elements);
set[loc] gatherValues(Expression e:null())
	= {indendentValue + "null"};
set[loc] gatherValues(Expression e:number(n))
	= {indendentValue + n};
set[loc] gatherValues(Expression e:booleanLiteral(b)){
	if(b)
		return {indendentValue + "true"};
	else
		return {indendentValue + "false"};
}
set[loc] gatherValues(Expression e:stringLiteral(s))
	= {indendentValue + s};
set[loc] gatherValues(Expression e:infix(lhs, _, rhs, exts))
	= gatherValues(lhs) + gatherValues(rhs) + gatherValues(exts);
set[loc] gatherValues(Expression e:prefix(_, operand))
	= gatherValues(operand);
set[loc] gatherValues(Expression e:postfix(operand,_))
	= gatherValues(operand);
default set[loc] gatherValues(Expression e)
	= {};
	
bool isDataAccess(Stmt s:acquireLock(_,_,_)) = false;
bool isDataAccess(Stmt s:releaseLock(_,_,_)) = false;
bool isDataAccess(Stmt s:entryPoint(_,_)) = false;
bool isDataAccess(Stmt s:exitPoint(_,_)) = false;
default bool isDataAccess(Stmt s) = true;

loc getIdFromStmt(Stmt::read(id, _, _)) = id;
loc getIdFromStmt(Stmt::create(id, _, _)) = id;
loc getIdFromStmt(Stmt::assign(id, _, _)) = id;
loc getIdFromStmt(Stmt::call(id, _, _, _)) = id;
loc getIdFromStmt(Stmt::releaseLock(id, _, _)) = id;
loc getIdFromStmt(Stmt::acquireLock(id, _, _)) = id;
loc getIdFromStmt(Stmt::entryPoint(id, _)) = id;
loc getIdFromStmt(Stmt::exitPoint(id, _)) = id;
loc getIdFromStmt(Stmt::change(id, _, _)) = id;

loc getDependencyFromStmt(Stmt::read(_, _, d)) = d;
loc getDependencyFromStmt(Stmt::create(_, _, p)) = p;
loc getDependencyFromStmt(Stmt::assign(_, _, r)) = r;
loc getDependencyFromStmt(Stmt::call(_, _, _, p)) = p;
loc getDependencyFromStmt(Stmt::releaseLock(_, _, s)) = s;
loc getDependencyFromStmt(Stmt::acquireLock(_, _, s)) = s;
//the (1,1) is needed to exclude it from the new ids
loc getDependencyFromStmt(Stmt::entryPoint(_, _)) = emptyId(1,1);
loc getDependencyFromStmt(Stmt::exitPoint(_, _)) = emptyId(1,1);

loc getDeclFromRead(Stmt::read(_,decl,_)) = decl;

loc getVarFromStmt(Stmt::read(_, var, _)) = var;
loc getVarFromStmt(Stmt::create(_, var, _)) = var;
loc getVarFromStmt(Stmt::assign(_, var, _)) = var;
loc getVarFromStmt(Stmt::call(_, var, _, _)) = var;
loc getVarFromStmt(Stmt::releaseLock(_, var, _)) = var;
loc getVarFromStmt(Stmt::acquireLock(_, var, _)) = var;
loc getVarFromStmt(Stmt::entryPoint(_, var)) = var;
loc getVarFromStmt(Stmt::exitPoint(_, var)) = var;
loc getVarFromStmt(Stmt::change(_, var, _)) = var;

set[Stmt] getSynchronizationActions(Program p)
	= {s | s <- p.statements, !isDataAccess(s)};
	
str extractClassName(loc method) 
	= substring(method.path,0,findLast(method.path,"/"));
	
set[loc] getDependencyIds(set[Stmt] potential)
	= { id | Stmt::read(id, _, _) <- potential}
	+  { id | Stmt::call(id, _, _) <- potential}
	+  { id | Stmt::create(id, _, _) <- potential}
	;	

loc getClassDeclFromType(TypeSymbol c:class(decl, []))
	= decl;

bool isClass(TypeSymbol c:class(_,_))
	= true;
default bool isClass(TypeSymbol c)
	= false;
	
bool isField(loc decl) = decl.scheme == "java+field";