module lang::sccfg::converter::util::Getters

import lang::sccfg::ast::DataFlowLanguage;

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
loc getIdFromStmt(Stmt::entryPoint(id, _, _)) = id;
loc getIdFromStmt(Stmt::exitPoint(id, _, _)) = id;

loc getDependencyFromStmt(Stmt::read(_, _, d)) = d;
loc getDependencyFromStmt(Stmt::create(_, _, p)) = p;
loc getDependencyFromStmt(Stmt::assign(_, _, r)) = r;
loc getDependencyFromStmt(Stmt::call(_, _, _, p)) = p;
loc getDependencyFromStmt(Stmt::releaseLock(_, _, s)) = s;
loc getDependencyFromStmt(Stmt::acquireLock(_, _, s)) = s;
loc getDependencyFromStmt(Stmt::entryPoint(_, _)) = emptyId;
loc getDependencyFromStmt(Stmt::exitPoint(_, _)) = emptyId;

loc getDeclFromRead(Stmt::read(_,decl,_)) = decl;

loc getVarFromStmt(Stmt::read(_, var, _)) = var;
loc getVarFromStmt(Stmt::create(_, var, _)) = var;
loc getVarFromStmt(Stmt::assign(_, var, _)) = var;
loc getVarFromStmt(Stmt::call(_, var, _, _)) = var;
loc getVarFromStmt(Stmt::releaseLock(_, var, _)) = var;
loc getVarFromStmt(Stmt::acquireLock(_, var, _)) = var;
loc getVarFromStmt(Stmt::entryPoint(_, var)) = var;
loc getVarFromStmt(Stmt::exitPoint(_, var)) = var;

set[Stmt] getSynchronizationActions(Program p)
	= {s | s <- p.statements, !isDataAccess(s)};