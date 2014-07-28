module lang::sdfg::converter::GatherStmtFromExpressions

import IO;
import String;
import lang::java::jdt::m3::AST;
import lang::java::m3::TypeSymbol;

import lang::sdfg::ast::SynchronizedDataFlowGraphLanguage;

import lang::sdfg::converter::util::State;
import lang::sdfg::converter::util::Getters;
import lang::sdfg::converter::util::ExceptionManagement;
import lang::sdfg::converter::util::EnvironmentManagement;
import lang::sdfg::converter::util::TypeSensitiveEnvironment;

//The functions are ordered according to the rascal/src/org/rascalImpl/library/lang/java/m3/AST.rsc [last accessed 13/5/2014]

//arrayAccess(Expression array, Expression index)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[loc, TypeSensitiveEnvironment], rel[loc,loc], map[str, State]] gatherStmtFromExpressions(Expression e:arrayAccess(ar, index), map[loc,set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts) {
	<stmts, indexRead, env, typesOf, acquireActions, exs> = gatherStmtFromExpressions(index, env, typesOf, volatileFields, acquireActions, stmts);
	stmts += indexRead;
	acquireActions += extractAcquireActions(indexRead, volatileFields);
	
	potential = addAndLock({Stmt::read(ar@src, ar@decl, id) | id <- getDataDependencyIds(indexRead)}
						  +{Stmt::read(ar@src, ar@decl, id) | id <- gatherValues(index)}
						   , acquireActions); 
	
	return <stmts, potential, env, typesOf, acquireActions, exs>;
}

//newArray(Type type, list[Expression] dimensions, Expression init)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[loc, TypeSensitiveEnvironment], rel[loc,loc], map[str, State]] gatherStmtFromExpressions(Expression e:newArray(_, dimensions, init), map[loc,set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts) {
	potential = {};
	exs = ();
	for(d <- dimensions) {
		<stmts, potentialD, env, typesOf, acquireActions, exsD> = gatherStmtFromExpressions(d, env, typesOf, volatileFields, acquireActions, stmts);
		exs = mergeExceptions(exs,exsD);
		potential += potentialD;
		stmts += potentialD;
		acquireActions += extractAcquireActions(potentialD, volatileFields);
	}
	
	<stmts, potentialI, env, typesOf, acquireActions, exsI> = gatherStmtFromExpressions(init, env, typesOf, volatileFields, acquireActions, stmts);
	exs = mergeExceptions(exs,exsI);
	stmts += potentialI;
	potential += potentialI;
	acquireActions += extractAcquireActions(potentialI, volatileFields);
		
	loc con = |java+constructor:///array|;
	potential = addAndLock({create(e@src, con, id) | id <- getDataDependencyIds(potential)}
						  +{create(e@src, con, id) | id <- gatherValues(dimensions)}
						  +{create(e@src, con, id) | id <- gatherValues(init)}
						  , acquireActions);
	if(potential == {})
		potential = addAndLock(create(e@src, con, emptyId), acquireActions);
	return <stmts, potential, env, typesOf, acquireActions, exs>;
}

//newArray(Type type, list[Expression] dimensions)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[loc, TypeSensitiveEnvironment], rel[loc,loc], map[str, State]] gatherStmtFromExpressions(Expression e:newArray(t, dimensions), map[loc,set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
potential = {};
	exs = ();
	for(d <- dimensions) {
		<stmts, potentialD, env, typesOf, acquireActions, exsD> = gatherStmtFromExpressions(d, env, typesOf, volatileFields, acquireActions, stmts);
		exs = mergeExceptions(exs,exsD);
		potential += potentialD;
		stmts += potentialD;
		acquireActions += extractAcquireActions(potentialD, volatileFields);
	}
		
	loc con = |java+constructor:///array|;
	potential = addAndLock({create(e@src, con, id) | id <- getDataDependencyIds(potential)}
						  +{create(e@src, con, id) | id <- gatherValues(dimensions)}
						  , acquireActions);
	return <stmts, potential, env, typesOf, acquireActions, exs>;
}

//arrayInitializer(list[Expression] elements)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[loc, TypeSensitiveEnvironment], rel[loc,loc], map[str, State]] gatherStmtFromExpressions(Expression e:arrayInitializer(list[Expression] elements), map[loc,set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts) {
	potential = {};
	exs = ();
	for(el <- elements) {
		<stmts, potentialC, env, typesOf, acquireActions, exsC> = gatherStmtFromExpressions(el, env, typesOf, volatileFields, acquireActions, stmts);
		exs = mergeExceptions(exs, exsC);
		potential += potentialC;
		stmts += potentialC;
		acquireActions += extractAcquireActions(potentialC, volatileFields);
	}
	loc con = |java+constructor:///array|;
	potential = addAndLock({create(e@src, con, id) | id <- getDataDependencyIds(potential)}
						  , acquireActions);
	return <stmts, potential, env, typesOf, acquireActions, exs>;
}

//assignment(Expression lhs, str operator, Expression rhs)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[loc, TypeSensitiveEnvironment], rel[loc,loc], map[str, State]] gatherStmtFromExpressions(Expression e:assignment(lhs,operator,rhs), map[loc,set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts) {
	iprintln(e);
	set[Stmt] potentialWrites = {};
	exsLhs = ();
	
	set[Stmt] potentialReads = {};
	exsRhs = ();
	
	set[loc] independentValues = gatherValues(rhs);
	
	if(operator != "=") {
		<stmts, potentialWrites, env, typesOf, acquireActions, exsLhs> = gatherStmtFromExpressions(lhs, env, typesOf, volatileFields, acquireActions, stmts);
		stmts += potentialWrites;
		acquireActions += extractAcquireActions(potentialWrites, volatileFields);
		
		<stmts, potentialReads, env, typesOf, acquireActions, exsRhs> = gatherStmtFromExpressions(rhs, env, typesOf, volatileFields, acquireActions, stmts);	
		stmts += potentialReads;
		acquireActions += extractAcquireActions(potentialReads, volatileFields);
		potentialReads += potentialWrites;
	}
	else{
		<stmts, potentialReads, env, typesOf, acquireActions, exsRhs> = gatherStmtFromExpressions(rhs, env, typesOf, volatileFields, acquireActions, stmts);	
		stmts += potentialReads;
		acquireActions += extractAcquireActions(potentialReads, volatileFields);
		
		<stmts, potentialWrites, env, typesOf, acquireActions, exsRhs> = gatherStmtFromExpressions(lhs, env, typesOf, volatileFields, acquireActions, stmts);
	}
	
	//Record the changes before locking the write
	if(qualifiedName(qName, n) := lhs || fieldAccess(_, qName, _) := lhs || qName:fieldAccess(_, _) := lhs) {
		<changed, env, typesOf> = gatherChangedClasses(qName, env, typesOf, e@src);
		stmts += addAndLock(changed, acquireActions);
	}
	else if(isArrayAccess(lhs)){
		stmts += addAndLock({Stmt::change(e@src, getTypeDeclFromTypeSymbol(lhs@typ), dep) | dep <- getDataDependencyIds(potentialReads)}
	                  	  + {Stmt::change(e@src, getTypeDeclFromTypeSymbol(lhs@typ), dep) | dep <- independentValues}
						  , acquireActions);
		env = updateAll(env, getDeclsFromTypeEnv(typesOf[getTypeDeclFromTypeSymbol(lhs@typ)] ? emptyTypeSensitiveEnvironment()), e@src);
		typesOf = update(typesOf, getTypeDeclFromTypeSymbol(lhs@typ), e@src);
		potential = addAndLock(potentialWrites, acquireActions);
		return <stmts, potential, env, typesOf, acquireActions, mergeExceptions(exsLhs, exsRhs)>;
	}
	else if(isField(lhs@decl)) {
		thisSrc = lhs@src;
		thisSrc.offset += 1;
		stmts += addAndLock({change(thisSrc, |java+class:///|+extractClassName(lhs@decl), e@src)} + {read(thisSrc,|java+class:///|+extractClassName(lhs@decl)+"/this", dep) | dep <- getDependenciesFromType(typesOf, |java+class:///|+extractClassName(lhs@decl))}, acquireActions);
		env = updateAll(env, getDeclsFromTypeEnv(typesOf[|java+class:///|+extractClassName(lhs@decl)] ? emptyTypeSensitiveEnvironment()), thisSrc);
		typesOf = update(typesOf, |java+class:///|+extractClassName(lhs@decl), thisSrc);
	}
	
	//get the variable name
	loc var;
	for(w:read(_, name, _) <- potentialWrites) {
		var = name;
	}
	
	if(var in volatileFields) 
		stmts += addAndUnlock(stmts, lhs@src, var);
		
	stmts += addAndLock({Stmt::assign(e@src, var, id) | id <- getDataDependencyIds(potentialReads)} 
	                  + {Stmt::assign(e@src, var, id) | id <- independentValues}
	                  , acquireActions);
	env[var] = {e@src};
	potential = addAndLock({Stmt::read(lhs@src, var, e@src)}, acquireActions);
	return <stmts, potential, env, typesOf, acquireActions, mergeExceptions(exsLhs, exsRhs)>;
}

//cast(Type type, Expression expression)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[loc, TypeSensitiveEnvironment], rel[loc,loc], map[str, State]] gatherStmtFromExpressions(Expression e:cast(_, exp), map[loc,set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts)
	= gatherStmtFromExpressions(exp, env, typesOf, volatileFields, acquireActions, stmts);

//newObject(Expression expr, Type type, list[Expression] args, Declaration class)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[loc, TypeSensitiveEnvironment], rel[loc,loc], map[str, State]] gatherStmtFromExpressions(Expression e:newObject(expr, _, args, _), map[loc,set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts)
	= gatherStmtFromExpressions(Expression::newObject(expr, args)[@decl = e@decl][@typ = e@typ][@src = e@src], env, typesOf, volatileFields, acquireActions, stmts);

//newObject(Expression expr, Type type, list[Expression] args)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[loc, TypeSensitiveEnvironment], rel[loc,loc], map[str, State]] gatherStmtFromExpressions(Expression e:newObject(Expression expr, _, list[Expression] args), map[loc,set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts)
	= gatherStmtFromExpressions(Expression::newObject(expr, args)[@decl = e@decl][@typ = e@typ][@src = e@src], env, typesOf, volatileFields, acquireActions, stmts);

//newObject(Expression expr, list[Expression] args, Declaration class)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[loc, TypeSensitiveEnvironment], rel[loc,loc], map[str, State]] gatherStmtFromExpressions(Expression e:newObject(Expression expr, list[Expression] args, _), map[loc,set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts)
	= gatherStmtFromExpressions(Expression::newObject(expr, args)[@decl = e@decl][@typ = e@typ][@src = e@src], env, typesOf, volatileFields, acquireActions, stmts);

//newObject(Expression expr, list[Expression] args)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[loc, TypeSensitiveEnvironment], rel[loc,loc], map[str, State]] gatherStmtFromExpressions(Expression e:newObject(expr, args), map[loc,set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts) {
	potential = {};
	exs = ();
	for(arg <- args) {
		<stmts, potential, env, typesOf, acquireActions, exsA> = gatherStmtFromExpressions(arg, env, typesOf, volatileFields, acquireActions, stmts);
		stmts += potential;
		acquireActions += extractAcquireActions(potential, volatileFields);
		exs = mergeExceptions(exs, exsA);
	}
	
	loc con = |java+constructor:///|;
	con.path = e@decl.path ? "";
	potential = addAndLock({create(e@src, con, id) | id <- getDataDependencyIds(potential)}
						  +{create(e@src, con, id) | id <- gatherValues(args)}
						  , acquireActions);
	if(potential == {})
		potential = addAndLock({create(e@src, con, emptyId)}, acquireActions);
	return <stmts, potential, env, typesOf, acquireActions, exs>;
}

//qualifiedName(Expression qualifier, Expression expression)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[loc, TypeSensitiveEnvironment], rel[loc,loc], map[str, State]] gatherStmtFromExpressions(Expression e:qualifiedName(q, exp), map[loc,set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts) {
	<stmts, potential, env, typesOf, acquireActions, exs> = gatherStmtFromExpressions(q, env, typesOf, volatileFields, acquireActions, stmts);
	stmts += potential;
	acquireActions += extractAcquireActions(potential, volatileFields);
	typesOf = addDeclOfType(typesOf, q@decl, q@typ);
	<stmts, potentialRead, env, typesOf, acquireActions, exsR> = gatherStmtFromExpressions(exp, env, typesOf, volatileFields, acquireActions, stmts);
	potentialRead += addAndLock({read(addr, var, id) | Stmt::read(addr, var, _) <- potentialRead, id <- getDataDependencyIds(potential)}, acquireActions);
	potentialRead -= {r | r:read(_,_,emptyId) <- potentialRead};
	return <stmts, potentialRead, env, typesOf, acquireActions, exs>;
}

//conditional(Expresion cond, Expression ifB, Expression elseB)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[loc, TypeSensitiveEnvironment], rel[loc,loc], map[str, State]] gatherStmtFromExpressions(Expression e:conditional(cond,ifB,elseB), map[loc,set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts) {
	<stmts, potential, env, typesOf, acquireActions, exs> = gatherStmtFromExpressions(cond, env, typesOf, volatileFields, acquireActions, stmts);
	stmts += potential;
	acquireActions += extractAcquireActions(potential, volatileFields);
	
	<stmts, potentialIf, envIf, typesIf, acquireActionsIf, exsIf> = gatherStmtFromExpressions(ifB, env, typesOf, volatileFields, acquireActions, stmts);	
	stmts += potentialIf;
	acquireActionsIf += extractAcquireActions(potentialIf, volatileFields);			
	
	<stmts, potentialElse, envElse, typesElse, acquireActionsElse, exsElse> = gatherStmtFromExpressions(elseB, env, typesOf, volatileFields, acquireActions, stmts);
	stmts += potentialElse;
	acquireActionsElse += extractAcquireActions(potentialElse, volatileFields);

	env = updateEnvironment(env,envIf);
	env = merge(env,envElse);
	exs = mergeExceptions(exs,exsIf);
	exs = mergeExceptions(exs,exsElse);
	typesOf = mergeTypesEnvironment(typesOf, typesIf);
	typesOf = mergeTypesEnvironment(typesOf, typesElse);
	return <stmts, potential + potentialIf + potentialElse, env, typesOf, acquireActionsIf + acquireActionsElse, exs>;
}

//fieldAccess(bool isSuper, Expression expression, str name)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[loc, TypeSensitiveEnvironment], rel[loc,loc], map[str, State]] gatherStmtFromExpressions(Expression e:fieldAccess(_,exp,_), map[loc,set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts) {
	<stmts, potential, env, typesOf, acquireActions, exs> = gatherStmtFromExpressions(exp, env, typesOf, volatileFields, acquireActions, stmts);
	stmts += potential;
	acquireActions += extractAcquireActions(potential, volatileFields);

	potential = addAndLock({Stmt::read(e@src, e@decl, writtenBy) | writtenBy <- env[e@decl] ? {emptyId}} 
						 + {Stmt::read(e@src, e@decl, getIdFromStmt(dependOn)) | dependOn <- potential}, 
						 acquireActions);	
	return <stmts, potential, env, typesOf, acquireActions, exs>;
}

//fieldAccess(bool isSuper, str name)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[loc, TypeSensitiveEnvironment], rel[loc,loc], map[str, State]] gatherStmtFromExpressions(Expression e:fieldAccess(isSuper, _), map[loc,set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts) {
	if(!isSuper) {
		assert false : "Field access without expression and not super!";
	}
	superSrc = e@src;
	superSrc.length = 5;
	stmts += addAndLock({Stmt::read(superSrc, |java+class:///|+extractClassName(e@decl)+"/super", dep) | dep <- getDependenciesFromType(typesOf, |java+class:///|+extractClassName(e@decl))}, acquireActions);
	
	potential = addAndLock({Stmt::read(e@src, e@decl, writtenBy) | writtenBy <- env[e@decl] ? {emptyId}}
						  +{Stmt::read(e@src, e@decl, superSrc)},
						    acquireActions);
	return <stmts, potential, env, typesOf, acquireActions, ()>;
}

//instanceof(Expression leftside, Type rightSide)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[loc, TypeSensitiveEnvironment], rel[loc,loc], map[str, State]] gatherStmtFromExpressions(Expression e:\instanceof(lhs,_), map[loc,set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts) {
	<stmts, potential, env, typesOf, acquireActions, exs> = gatherStmtFromExpressions(lhs, env, typesOf, volatileFields, acquireActions, stmts);
	stmts += potential;
	acquireActions += extractAcquireActions(potential, volatileFields);
	return <stmts, {}, env, typesOf, acquireActions, exs>;
}

//methodCall(bool isSuper, str name, list[Expression] arguments)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[loc, TypeSensitiveEnvironment], rel[loc,loc], map[str, State]] gatherStmtFromExpressions(Expression e:methodCall(isSuper,name,args), map[loc,set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts)
	= gatherStmtFromExpressions(methodCall(isSuper, Expression::this()[@src = e@src][@typ = class(|java+class:///|+extractClassName(e@decl),[])], name, args)[@decl = e@decl][@typ = e@typ][@src = e@src], env, typesOf, volatileFields, acquireActions, stmts);

//method(bool isSuper, Expression receiver, str name, list[Expression] arguments)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[loc, TypeSensitiveEnvironment], rel[loc,loc], map[str, State]] gatherStmtFromExpressions(Expression e:methodCall(isSuper, receiver, name, args), map[loc,set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts) {
	<stmts, potentialR, env, typesOf, acquireActions, exs> = gatherStmtFromExpressions(receiver, env, typesOf, volatileFields, acquireActions, stmts);
	stmts += potentialR;
	acquireActions += extractAcquireActions(potentialR, volatileFields);
	
	exs = ();
	potential = {};
	for(arg <- args) {
		<stmts, potentialA, env, typesOf, acquireActions, exsA> = gatherStmtFromExpressions(arg, env, typesOf, volatileFields, acquireActions, stmts);
		potential += potentialA;
		stmts += addAndLock(potentialA, acquireActions);
		acquireActions += extractAcquireActions(potentialA, volatileFields);
		exs = mergeExceptions(exs,exsA);
	}
	<changed, env, typesOf> = gatherChangedClasses(receiver, env, typesOf, e@src);
	stmts += addAndLock(changed, acquireActions);	
	
	loc recSrc;
	for(r:read(id, _, _) <- potentialR){
		recSrc = id;
	} 		
	potential = addAndLock({Stmt::call(e@src, recSrc, e@decl, arg) | arg <- getDataDependencyIds(potential)}
						   +{Stmt::call(e@src, recSrc, e@decl, arg) | arg <- gatherValues(args)}
						   , acquireActions);
						   
	//if the method call does not have any arguments
	if(potential == {})
		potential = addAndLock({Stmt::call(e@src, recSrc, e@decl, emptyId)}, acquireActions);
	stmts += potential;
	for(ex <- exceptions[e@decl] ? {}) {
		if(ex in exs) {
			exs[ex] = merge(exs[ex],state(env,typesOf,acquireActions));
		}
		else{
			exs[ex] = state(stmts, env,typesOf,acquireActions);
		}
	}
	return <stmts, potential, env, typesOf, acquireActions, exs>;
}

//variable(str name, int extraDimensions, Expression init)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[loc, TypeSensitiveEnvironment], rel[loc,loc], map[str, State]] gatherStmtFromExpressions(Expression e:variable(_, _, rhs), map[loc,set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts) {
	<stmts, potential, env, typesOf, acquireActions, exs> = gatherStmtFromExpressions(rhs, env, typesOf, volatileFields, acquireActions, stmts);
	stmts += potential;
	acquireActions += extractAcquireActions(potential, volatileFields);
	if(e@decl in volatileFields) {
		stmts += addAndUnlock(stmts, e@src, e@decl);
	}
	
	stmts += addAndLock({Stmt::assign(e@src, e@decl, id) | id <- getDataDependencyIds(potential)}
					   +{Stmt::assign(e@src, e@decl, id) | id <- gatherValues(rhs)}
					   , acquireActions);
	env[e@decl] = {e@src};
	return <stmts, {}, env, typesOf, acquireActions, exs>;
}

//bracket(Expression exp);
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[loc, TypeSensitiveEnvironment], rel[loc,loc], map[str, State]] gatherStmtFromExpressions(Expression e:\bracket(exp), map[loc,set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts)
	= gatherStmtFromExpressions(exp, env, typesOf, volatileFields, acquireActions, stmts);


//this() cannot change so maybe it is not needed here, but we need the depedency for the synchronized
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[loc, TypeSensitiveEnvironment], rel[loc,loc], map[str, State]] gatherStmtFromExpressions(Expression e:this(), map[loc,set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts) {
	potential = addAndLock({Stmt::read(e@src, getTypeDeclFromTypeSymbol(e@typ) + "/this", dep) | dep <- getDependenciesFromType(typesOf, getTypeDeclFromTypeSymbol(e@typ)) }, acquireActions);
	if(potential == {}){
		potential = addAndLock({Stmt::read(e@src, getTypeDeclFromTypeSymbol(e@typ) + "/this", emptyId)}, acquireActions);
	}
	return <stmts, potential, env, typesOf, acquireActions, ()>;
}

//this(Expression exp)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[loc, TypeSensitiveEnvironment], rel[loc,loc], map[str, State]] gatherStmtFromExpressions(Expression e:this(exp), map[loc,set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts) {
	assert false : "Found this with expression in: <e>!";
	return <stmts, {}, env, typesOf, acquireActions, ()>;
}

//super()
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[loc, TypeSensitiveEnvironment], rel[loc,loc], map[str, State]] gatherStmtFromExpressions(Expression e:super(), map[loc,set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts) {
	assert false : "Found super in: <e>!";
	return <stmts, {}, env, typesOf, acquireActions, ()>;
}

//declarationExpression(Declaration d)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[loc, TypeSensitiveEnvironment], rel[loc,loc], map[str, State]] gatherStmtFromExpressions(Declaration m , Expression e:declarationExpression(d), map[loc,set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts) {
	exs = ();
	fenv = emptyFlowEnvironment();
	top-down-break visit(d) {
		case Expression exp : {
			<stmts, _, env, typesOf, acquireActions, exsE> = gatherStmtFromExpressions(exp, env, typesOf, volatileFields, acquireActions, stmts);
			exs = mergeExceptions(exs, exsE);
		}
	}
	return <stmts, {}, env, typesOf, acquireActions, exs>;
}

//infix(Expression lhs, str operator, Expression rhs, list[Expression] extendedOperands)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[loc, TypeSensitiveEnvironment], rel[loc,loc], map[str, State]]  gatherStmtFromExpressions(e:infix(lhs, operator, rhs, ext), map[loc,set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts) {
	operands = [rhs] + ext;
	<stmts, potential, env, typesOf, acquireActions, exs> = gatherStmtFromExpressions(lhs, env, typesOf, volatileFields, acquireActions, stmts);
	stmts += potential;
	acquireActions += extractAcquireActions(potential, volatileFields);
	
	if(operator == "&&" || operator == "||") {	
		envOp = env;
		typesOp = typesOf;
		acquireActionsOp = acquireActions;
		for(op <- operands) {
			<stmts, potentialOp, envOp, typesOp, acquireActionsOp, exsOp> = gatherStmtFromExpressions(op, envOp, typesOp, volatileFields, acquireActionsOp, stmts);
			stmts += potentialOp;
			acquireActions += extractAcquireActions(potentialOp, volatileFields);
			env = merge(env,envOp);
			typesOp = mergeTypesEnvironment(typesOf, typesOp);
			exs = mergeExceptions(exs, exsOp);
			//The expressions are already in stmts, however we need to fill the potential for dependencies
			potential += potentialOp;
		}			
		return <stmts, potential, env, typesOf, acquireActions, exs>;
	}
	else{
		exs = ();
		dependencies = potential;
		for(op <- operands) {
			<stmts, potential, env, typesOf, acquireActions, exsOp> = gatherStmtFromExpressions(op, env, typesOf, volatileFields, acquireActions, stmts);
			stmts += potential;
			dependencies += potential;
			acquireActions += extractAcquireActions(potential, volatileFields);
			exs = mergeExceptions(exs,exsOp);
		}
		//the reads are not potential because there are operations done one them that cannot be statements!
		return <stmts, dependencies, env, typesOf, acquireActions, exs>;
	}
}

//postfix(Expression operand, str operator)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[loc, TypeSensitiveEnvironment], rel[loc,loc], map[str, State]]  gatherStmtFromExpressions(Expression e:postfix(operand, operator), map[loc,set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts) {
	if(operator == "++" || operator == "--") {
		<stmts, potential, env, typesOf, acquireActions, exs> = gatherStmtFromExpressions(operand, env, typesOf, volatileFields, acquireActions, stmts);
		stmts += potential;
		acquireActions += extractAcquireActions(potential, volatileFields);
		
		//Record the changes before locking the write
		if(qualifiedName(qName, n) := operand || fieldAccess(_, qName, _) := operand) {
			<changed, env, typesOf> = gatherChangedClasses(qName, env, typesOf,e@src);
			stmts += addAndLock(changed, acquireActions);
		}
		else if(isArrayAccess(operand)){
			stmts += addAndLock({Stmt::change(e@src, getTypeDeclFromTypeSymbol(operand@typ), dep) | dep <- getDataDependencyIds(potential)}
	        	          	  + {Stmt::change(e@src, getTypeDeclFromTypeSymbol(operand@typ), |value:///1|)}
							  , acquireActions);
			env = updateAll(env, getDeclsFromTypeEnv(typesOf[getTypeDeclFromTypeSymbol(operand@typ)] ? emptyTypeSensitiveEnvironment()), e@src);
			typesOf = update(typesOf, getTypeDeclFromTypeSymbol(operand@typ), e@src);
			potential = addAndLock(potential, acquireActions);
			return <stmts, potential, env, typesOf, acquireActions, exs>;
		}
		else if(isField(operand@decl)) {
			thisSrc = operand@src;
			thisSrc.offset += 1;
			stmts += addAndLock({change(thisSrc, |java+class:///|+extractClassName(operand@decl), thisSrc)} + {read(thisSrc,|java+class:///|+extractClassName(operand@decl)+"/this", dep) | dep <- getDependenciesFromType(typesOf, |java+class:///|+extractClassName(operand@decl))}, acquireActions);
			env = updateAll(env, getDeclsFromTypeEnv(typesOf[|java+class:///|+extractClassName(operand@decl)]), thisSrc);
			typesOf = update(typesOf, |java+class:///|+extractClassName(operand@decl), thisSrc);
		}
		if(operand@decl in volatileFields) {
			stmts += addAndUnlock(stmts, e@src, operand@decl);
		}
		
		stmts += addAndLock({Stmt::assign(e@src, operand@decl, |value:///1|)} + {Stmt::assign(e@src, operand@decl, id) | id <- getDataDependencyIds(potential)}, acquireActions);
		
		//potential was already found
		env[operand@decl] = {e@src};
	
		return <stmts, potential, env, typesOf, acquireActions, exs>;
	}
	else{
		return gatherStmtFromExpressions(operand, env, typesOf, volatileFields, acquireActions, stmts);
	}
}

//prefix(str operator, Expression operand)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[loc, TypeSensitiveEnvironment], rel[loc,loc], map[str, State]] gatherStmtFromExpressions(Expression e:prefix(operator, operand), map[loc,set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts) {
	if(operator == "++" || operator == "--") {
		<stmts, potential, env, typesOf, acquireActions, exs> = gatherStmtFromExpressions(operand, env, typesOf, volatileFields, acquireActions, stmts);
		stmts += potential;
		acquireActions += extractAcquireActions(potential, volatileFields);
		
		//Record the changes before locking the write
		if(qualifiedName(qName, n) := operand || fieldAccess(_, qName, _) := operand) {
			<changed, env, typesOf> = gatherChangedClasses(qName, env, typesOf, e@src);
			stmts += addAndLock(changed, acquireActions);
		}
		else if(isArrayAccess(operand)){
			stmts += addAndLock({Stmt::change(e@src, getTypeDeclFromTypeSymbol(operand@typ), dep) | dep <- getDataDependencyIds(potential)}
	        	          	  + {Stmt::change(e@src, getTypeDeclFromTypeSymbol(operand@typ), |value:///1|)}
							  , acquireActions);
			env = updateAll(env, getDeclsFromTypeEnv(typesOf[getTypeDeclFromTypeSymbol(operand@typ)] ? emptyTypeSensitiveEnvironment()), e@src);
			typesOf = update(typesOf, getTypeDeclFromTypeSymbol(operand@typ), e@src);
			potential = addAndLock(potential, acquireActions);
			return <stmts, potential, env, typesOf, acquireActions, exs>;
		}
		else if(isField(operand@decl)) {
			thisSrc = operand@src;
			thisSrc.offset += 1;
			stmts += addAndLock({change(thisSrc, |java+class:///|+extractClassName(operand@decl), thisSrc)} + {read(thisSrc,|java+class:///|+extractClassName(operand@decl)+"/this", dep) | dep <- getDependenciesFromType(typesOf, |java+class:///|+extractClassName(operand@decl))}, acquireActions);
			env = updateAll(env, getDeclsFromTypeEnv(typesOf[|java+class:///|+extractClassName(operand@decl)]), thisSrc);
			typesOf = update(typesOf, |java+class:///|+extractClassName(operand@decl), thisSrc);
		}
	
		stmts += addAndLock({Stmt::assign(e@src, operand@decl, id) | id <- getDataDependencyIds(potential)}, acquireActions);
		env[operand@decl] = {e@src};
		
		potential = addAndLock({Stmt::read(operand@src, operand@decl, e@src)}, acquireActions);
		return <stmts, potential, env, typesOf, acquireActions, exs>;
	}
	else{
		return gatherStmtFromExpressions(operand, env, typesOf, volatileFields, acquireActions, stmts);
	}
}

//simpleName(str name)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[loc, TypeSensitiveEnvironment], rel[loc,loc], map[str, State]] gatherStmtFromExpressions(Expression e:simpleName(name), map[loc,set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts) {
	potential = addAndLock({Stmt::read(e@src, e@decl, writtenBy) | writtenBy <- env[e@decl] ? {emptyId}}, acquireActions);	
	return <stmts, potential, env, typesOf, acquireActions, ()>;
}

//type(simpleType(_)) representing <Object>.class no check for volatile required
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[loc, TypeSensitiveEnvironment], rel[loc,loc], map[str, State]] gatherStmtFromExpressions(Expression e:\type(simpleType(name)), map[loc,set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts) {
	loc l = name@decl;
	l.path = name@decl.path + ".class";
	potential = addAndLock({Stmt::read(e@src, l, emptyId)}, acquireActions);	
	return <stmts, potential, env, typesOf, acquireActions, ()>;
}

default tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[loc, TypeSensitiveEnvironment], rel[loc,loc], map[str, State]] gatherStmtFromExpressions(Expression e, map[loc,set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts) {
	//assert false : "Unknown expression <e>";
	return <stmts, {}, env, typesOf, acquireActions, ()>;
}



set[Stmt] addAndLock(set[Stmt] newStmts, rel[loc,loc] acquireActions)
	= newStmts + {Stmt::acquireLock(idL, l, getIdFromStmt(s)) | s <- newStmts, <idL, l> <- acquireActions};

set[Stmt] addAndUnlock(set[Stmt] newStmts, loc idL, loc l) {
	return newStmts + {Stmt::releaseLock(idL, l, getIdFromStmt(s)) | s <- newStmts};
}
rel[loc, loc] extractAcquireActions(set[Stmt] potential, set[loc] volFields)
	= { <id, var> |  read(id, var, _) <- potential, var in volFields};

tuple[set[Stmt], map[loc,set[loc]], map[loc, TypeSensitiveEnvironment]] gatherChangedClasses(Expression e:simpleName(_), map[loc,set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, loc dep)
	=  <{change(e@src, getTypeDeclFromTypeSymbol(e@typ), dep)}, updateAll(env, getDeclsFromTypeEnv(typesOf[getTypeDeclFromTypeSymbol(e@typ)]?emptyTypeSensitiveEnvironment()), e@src), update(typesOf, getTypeDeclFromTypeSymbol(e@typ), e@src)>;
tuple[set[Stmt], map[loc,set[loc]], map[loc, TypeSensitiveEnvironment]] gatherChangedClasses(Expression q:qualifiedName(exp, name), map[loc,set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, loc dep) {
	<newStmts, env, typesOf> = gatherChangedClasses(exp, env, typesOf, dep);
	return <{change(name@src, getTypeDeclFromTypeSymbol(name@typ), dep)} + newStmts, updateAll(env, getDeclsFromTypeEnv(typesOf[getTypeDeclFromTypeSymbol(name@typ)] ? emptyTypeSensitiveEnvironment()), name@src), update(typesOf, getTypeDeclFromTypeSymbol(name@typ), name@src)>;
}

tuple[set[Stmt], map[loc,set[loc]], map[loc, TypeSensitiveEnvironment]] gatherChangedClasses(Expression e:this(), map[loc,set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, loc dep)
	= <{change(e@src, getTypeDeclFromTypeSymbol(e@typ), dep)}, updateAll(env, getDeclsFromTypeEnv(typesOf[getTypeDeclFromTypeSymbol(e@typ)]?emptyTypeSensitiveEnvironment()), e@src), update(typesOf, getTypeDeclFromTypeSymbol(e@typ), e@src)>;
	
tuple[set[Stmt], map[loc,set[loc]], map[loc, TypeSensitiveEnvironment]] gatherChangedClasses(Expression e:fieldAccess(true, _), map[loc,set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, loc dep) {
	superSrc = e@src;
	superSrc.length = 5;
	return <{change(superSrc, |java+class:///|+extractClassName(e@decl), dep)}, updateAll(env, getDeclsFromTypeEnv(typesOf[|java+class:///|+extractClassName(e@decl)]), superSrc), update(typesOf, |java+class:///|+extractClassName(e@decl), superSrc)>;
}
tuple[set[Stmt], map[loc,set[loc]], map[loc, TypeSensitiveEnvironment]] gatherChangedClasses(Expression f:fieldAccess(_, exp, name), map[loc,set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf) {
	<newStmts, env, typesOf> = gatherChangedClasses(exp, env, typesOf, dep);
	return <{change(f@src, getTypeDeclFromTypeSymbol(f@typ), dep)} + newStmts, updateAll(env, getDeclsFromTypeEnv(typesOf[getTypeDeclFromTypeSymbol(f@typ)]?emptyTypeSensitiveEnvironment()), f@src), update(typesOf, getTypeDeclFromTypeSymbol(f@typ), f@src)>;
}

bool isArrayAccess(Expression a:arrayAccess(_,_)) = true;
default bool isArrayAccess(Expression lhs) = false;