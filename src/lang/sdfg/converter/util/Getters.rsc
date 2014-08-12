module lang::sdfg::converter::util::Getters

import Set;
import String;

import lang::java::jdt::m3::AST;
import lang::java::m3::TypeSymbol;

import lang::sdfg::ast::SynchronizedDataFlowGraphLanguage;
import lang::sdfg::converter::util::EnvironmentManagement;
import lang::sdfg::converter::util::TypeSensitiveEnvironment;

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
	= {s | s <- p.stmts, isSyncDependency(s)};
	
str extractClassName(loc method) 
	= substring(method.path,0,findLast(method.path,"/"));
	
set[loc] getDataDependencyIds(set[Stmt] potential)
	= { id | Stmt::read(id, _, _) <- potential}
	+ { id | Stmt::call(id, _, _, _) <- potential}
	+ { id | Stmt::create(id, _, _) <- potential}
	;	

set[loc] getAllDependenciesIds(set[Stmt] potential)
	= { id 		| Stmt::read(_, _, id) <- potential}
	+ { r, id 	| Stmt::call(_, r, _, id) <- potential}
	+ { id 		| Stmt::create(_, _, id) <- potential}
	+ { id		| Stmt::change(_, _, id) <- potential}
	+ { id		| Stmt::assign(_, _, id) <- potential}
	+ { id		| Stmt::acquireLock(id, _, _) <- potential}
	+ { id		| Stmt::releaseLock(id, _, _) <- potential}
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
default bool isSyncDependency(Stmt s) = false;

bool isClass(TypeSymbol c:class(_,_))
	= true;
default bool isClass(TypeSymbol c)
	= false;
	
bool isField(loc decl) = decl.scheme == "java+field";
bool isParameter(loc decl) = decl.scheme == "java+parameter";
bool isVariable(loc decl) = decl.scheme == "java+variable";


bool isArrayAccess(Expression a:arrayAccess(_,_)) = true;
default bool isArrayAccess(Expression lhs) = false;

set[Stmt] addAndLock(set[Stmt] newStmts, rel[loc,loc] acquireActions)
	= newStmts + {Stmt::acquireLock(idL, l, getIdFromStmt(s)) | s <- newStmts, <idL, l> <- acquireActions};

set[Stmt] addAndUnlock(set[Stmt] newStmts, loc idL, loc l) {
	return newStmts + {Stmt::releaseLock(idL, l, getIdFromStmt(s)) | s <- newStmts};
}
rel[loc, loc] extractAcquireActions(set[Stmt] potential, set[loc] volFields)
	= { <id, var> |  read(id, var, _) <- potential, var in volFields};

tuple[set[Stmt], map[loc,set[loc]], map[loc, TypeSensitiveEnvironment]] gatherChangedClasses(Expression e:simpleName(_), map[loc,set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, loc dep){
	changed = {};
	if(isField(e@decl)){
		thisSrc = e@src;
		thisSrc.offset += 1;
		changed += {change(thisSrc, |java+class:///|+extractClassName(e@decl), e@src)} + {read(thisSrc,|java+class:///|+extractClassName(e@decl)+"/this", dep) | dep <- getDependenciesFromType(typesOf, |java+class:///|+extractClassName(e@decl))};
		env = updateAll(env, getDeclsFromTypeEnv(typesOf[|java+class:///|+extractClassName(e@decl)]?emptyTypeSensitiveEnvironment()), thisSrc);
		typesOf = update(typesOf, |java+class:///|+extractClassName(e@decl), thisSrc);
	}
	changed += {change(e@src, getTypeDeclFromTypeSymbol(e@typ), dep)};
	return  <changed, updateAll(env, getDeclsFromTypeEnv(typesOf[getTypeDeclFromTypeSymbol(e@typ)]?emptyTypeSensitiveEnvironment()), e@src), update(typesOf, getTypeDeclFromTypeSymbol(e@typ), e@src)>;
}
tuple[set[Stmt], map[loc,set[loc]], map[loc, TypeSensitiveEnvironment], loc] gatherChangedClasses(Expression q:qualifiedName(exp, name), map[loc,set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, loc dep) {
	<newStmts, env, typesOf> = gatherChangedClasses(exp, env, typesOf, name@src);
	return <{change(name@src, getTypeDeclFromTypeSymbol(name@typ), dep)} + newStmts, updateAll(env, getDeclsFromTypeEnv(typesOf[getTypeDeclFromTypeSymbol(name@typ)] ? emptyTypeSensitiveEnvironment()), name@src), update(typesOf, getTypeDeclFromTypeSymbol(name@typ), name@src)>;
}

tuple[set[Stmt], map[loc,set[loc]], map[loc, TypeSensitiveEnvironment]] gatherChangedClasses(Expression e:this(), map[loc,set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, loc dep)
	= <{change(e@src, getTypeDeclFromTypeSymbol(e@typ), dep)}, updateAll(env, getDeclsFromTypeEnv(typesOf[getTypeDeclFromTypeSymbol(e@typ)]?emptyTypeSensitiveEnvironment()), e@src), update(typesOf, getTypeDeclFromTypeSymbol(e@typ), e@src)>;
	
tuple[set[Stmt], map[loc,set[loc]], map[loc, TypeSensitiveEnvironment]] gatherChangedClasses(Expression e:fieldAccess(true, _), map[loc,set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, loc dep) {
	superSrc = e@src;
	superSrc.length = 5;
	return <{change(superSrc, |java+class:///|+extractClassName(e@decl), dep)}, updateAll(env, getDeclsFromTypeEnv(typesOf[|java+class:///|+extractClassName(e@decl)]), superSrc), update(typesOf, |java+class:///|+extractClassName(e@decl),e@src)>;
}

tuple[set[Stmt], map[loc,set[loc]], map[loc, TypeSensitiveEnvironment]] gatherChangedClasses(Expression e:fieldAccess(false, _), map[loc,set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, loc dep)
	= <{change(e@src, |java+class:///|+extractClassName(e@decl), dep)}, updateAll(env, getDeclsFromTypeEnv(typesOf[|java+class:///|+extractClassName(e@decl)]), e@src), update(typesOf, |java+class:///|+extractClassName(e@decl))>;

tuple[set[Stmt], map[loc,set[loc]], map[loc, TypeSensitiveEnvironment]] gatherChangedClasses(Expression f:fieldAccess(_, exp, name), map[loc,set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, loc dep) {
	<newStmts, env, typesOf> = gatherChangedClasses(exp, env, typesOf, f@src);
	return <{change(f@src, getTypeDeclFromTypeSymbol(f@typ), dep)} + newStmts, updateAll(env, getDeclsFromTypeEnv(typesOf[getTypeDeclFromTypeSymbol(f@typ)]?emptyTypeSensitiveEnvironment()), f@src), update(typesOf, getTypeDeclFromTypeSymbol(f@typ), f@src)>;
}

tuple[set[Stmt], map[loc,set[loc]], map[loc, TypeSensitiveEnvironment]] propagateChanges(Expression q:qualifiedName(qName, n), map[loc,set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, loc dep)
	= gatherChangedClasses(qName, env, typesOf, n@src);
tuple[set[Stmt], map[loc,set[loc]], map[loc, TypeSensitiveEnvironment]] propagateChanges(Expression q:simpleName(_), map[loc,set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, loc dep){
	changed = {};
	if(isField(q@decl)){
		thisSrc = q@src;
		thisSrc.offset += 1;
		changed += {change(thisSrc, |java+class:///|+extractClassName(q@decl), q@src)} + {read(thisSrc,|java+class:///|+extractClassName(q@decl)+"/this", dep) | dep <- getDependenciesFromType(typesOf, |java+class:///|+extractClassName(q@decl))};
		env = updateAll(env, getDeclsFromTypeEnv(typesOf[|java+class:///|+extractClassName(q@decl)]?emptyTypeSensitiveEnvironment()), thisSrc);
		typesOf = update(typesOf, |java+class:///|+extractClassName(q@decl), thisSrc);	
	}
	return <changed, env, typesOf>;
}
tuple[set[Stmt], map[loc,set[loc]], map[loc, TypeSensitiveEnvironment]] propagateChanges(Expression f:fieldAccess(_, qName, _), map[loc,set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, loc dep)
	= gatherChangedClasses(qName, env, typesOf, f@src);
tuple[set[Stmt], map[loc,set[loc]], map[loc, TypeSensitiveEnvironment]] propagateChanges(Expression qName:fieldAccess(_, _), map[loc,set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, loc dep)
	= gatherChangedClasses(qName, env, typesOf, dep);
tuple[set[Stmt], map[loc,set[loc]], map[loc, TypeSensitiveEnvironment]] propagateChanges(Expression qName:arrayAccess(arr, _), map[loc,set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, loc dep)
	= propagateChanges(arr, env, typesOf, arr@src);
default tuple[set[Stmt], map[loc,set[loc]], map[loc, TypeSensitiveEnvironment]] propagateChanges(Expression e, map[loc,set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, loc dep)
	= <{}, env, typesOf>;
	
	
bool breakingControlFlow(Statement s:\continue()) = true;
bool breakingControlFlow(Statement s:\break()) = true;
bool breakingControlFlow(Statement s:\break("")) = true;
bool breakingControlFlow(Statement s:\return()) = true;
bool breakingControlFlow(Statement s:\return(_)) = true;
bool breakingControlFlow(Statement s:\throw(_)) = true;
default bool breakingControlFlow(Statement s) =  false;