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
	
	<stmts, potential, env, typesOf, acquireActions, exs> = gatherStmtFromExpressions(ar, env, typesOf, volatileFields, acquireActions, stmts);
	stmts += potential;
	acquireActions += extractAcquireActions(potential, volatileFields);
	decl = ar@decl;
	potential = addAndLock({Stmt::read(id, ar@decl, dep) | Stmt::read(id, decl,_) <- potential, dep <- getDataDependencyIds(indexRead)}
						  +{Stmt::read(id, ar@decl, dep) | Stmt::read(id, decl,_) <- potential, dep<- gatherValues(index)}
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
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[loc, TypeSensitiveEnvironment], rel[loc,loc], map[str, State]] gatherStmtFromExpressions(Expression e:newArray(t, dimensions), map[loc,set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts) {
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
	if(operator != "=") {
		rhs = infix(lhs, "+", rhs,[])[@src = e@src][@typ = e@typ];
	}
	return resolveAssignment(lhs, rhs, env, typesOf, volatileFields, acquireActions, stmts, e@src);
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
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[loc, TypeSensitiveEnvironment], rel[loc,loc], map[str, State]] gatherStmtFromExpressions(Expression e:methodCall(isSuper,name,args), map[loc,set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts) {
	thisSrc = e@src;
	thisSrc.offset = thisSrc.offset+1;
	return gatherStmtFromExpressions(methodCall(isSuper, Expression::this()[@src = thisSrc][@typ = class(|java+class:///|+extractClassName(e@decl),[])], name, args)[@decl = e@decl][@typ = e@typ][@src = e@src], env, typesOf, volatileFields, acquireActions, stmts);
}
//methodCall(bool isSuper, Expression receiver, str name, list[Expression] arguments)
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
	for(arg <- args) {
		<changed, env, typesOf> = propagateChanges(arg, env, typesOf, e@src);
		stmts += addAndLock(changed, acquireActions);
	}
	<changed, env, typesOf> = propagateChanges(receiver, env, typesOf, e@src);
	stmts += addAndLock(changed, acquireActions);	
	
	loc recSrc;
	for(r:read(id, var, _) <- potentialR) {
		recSrc = id;
		if(isField(var) || isParameter(var) || isVariable(var)){
			stmts += addAndLock({change(id, getTypeDeclFromTypeSymbol(receiver@typ), e@src)}, acquireActions);
			env = updateAll(env, getDeclsFromTypeEnv(typesOf[getTypeDeclFromTypeSymbol(receiver@typ)]?emptyTypeSensitiveEnvironment()), id);
			typesOf = update(typesOf, getTypeDeclFromTypeSymbol(receiver@typ), id);	
			break;
		}
	} 
	<changed, env, typesOf> = propagateChanges(receiver, env, typesOf, e@src);
	stmts += addAndLock(changed, acquireActions);	
	for(r:create(id, _, _) <- potentialR) {
		recSrc = id;
	} 
	for(r:call(id, _, _) <- potentialR) {
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
	typesOf = addDeclOfType(typesOf, e@decl, e@typ);
	return <stmts, {}, env, typesOf, acquireActions, exs>;
}

//bracket(Expression exp);
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[loc, TypeSensitiveEnvironment], rel[loc,loc], map[str, State]] gatherStmtFromExpressions(Expression e:\bracket(exp), map[loc,set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts)
	= gatherStmtFromExpressions(exp, env, typesOf, volatileFields, acquireActions, stmts);


//this() cannot change so maybe it is not needed here, but we need the depedency for the synchronized
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[loc, TypeSensitiveEnvironment], rel[loc,loc], map[str, State]] gatherStmtFromExpressions(Expression e:this(), map[loc,set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts) {
	potential = addAndLock({Stmt::read(e@src, |java+parameter:///| + getTypeDeclFromTypeSymbol(e@typ).path + "/this", dep) | dep <- getDependenciesFromType(typesOf, getTypeDeclFromTypeSymbol(e@typ)) }, acquireActions);
	if(potential == {}) {
		potential = addAndLock({Stmt::read(e@src, |java+parameter:///| + getTypeDeclFromTypeSymbol(e@typ).path + "/this", emptyId)}, acquireActions);
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
		rhs = infix(operand, "+", number("1")[@src = e@src][@typ = e@typ],[])[@src = e@src][@typ = e@typ];
		return resolveAssignment(operand, rhs, env, typesOf, volatileFields, acquireActions, stmts, e@src);
	}
	else{
		return gatherStmtFromExpressions(operand, env, typesOf, volatileFields, acquireActions, stmts);
	}
}

//prefix(str operator, Expression operand)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[loc, TypeSensitiveEnvironment], rel[loc,loc], map[str, State]] gatherStmtFromExpressions(Expression e:prefix(operator, operand), map[loc,set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts) {
	if(operator == "++" || operator == "--") {
		rhs = infix(operand, "+", number("1")[@src = e@src][@typ = e@typ],[])[@src = e@src][@typ = e@typ];
		return resolveAssignment(operand, rhs, env, typesOf, volatileFields, acquireActions, stmts, e@src);
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
	
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[loc, TypeSensitiveEnvironment], rel[loc,loc], map[str, State]] resolveAssignment(Expression target, Expression rhs, map[loc,set[loc]] env, map[loc, TypeSensitiveEnvironment] typesOf, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts, loc dep) {
	set[loc] independentValues = gatherValues(rhs);	
	<stmts, potentialReads, env, typesOf, acquireActions, exsRhs> = gatherStmtFromExpressions(rhs, env, typesOf, volatileFields, acquireActions, stmts);	
	stmts += potentialReads;
	acquireActions += extractAcquireActions(potentialReads, volatileFields);
		
	<stmts, potentialWrites, env, typesOf, acquireActions, exsLhs> = gatherStmtFromExpressions(target, env, typesOf, volatileFields, acquireActions, stmts);
	
	if(arrayAccess(arr,_) := target) {
		decl = arr@decl;
		<changed, env, typesOf> = propagateChanges(target, env, typesOf, dep);
		stmts += addAndLock(changed
						  + {Stmt::change(id, getTypeDeclFromTypeSymbol(arr@typ), d) | Stmt::read(id, decl,_)<- potentialWrites, d <- getDataDependencyIds(potentialReads)}
	                  	  + {Stmt::change(id, getTypeDeclFromTypeSymbol(arr@typ), d) | Stmt::read(id, decl,_)<- potentialWrites, d <- independentValues}
						  , acquireActions);
		env = updateAll(env, getDeclsFromTypeEnv(typesOf[getTypeDeclFromTypeSymbol(arr@typ)] ? emptyTypeSensitiveEnvironment()), dep);
		typesOf = update(typesOf, getTypeDeclFromTypeSymbol(arr@typ), dep);
		potential = addAndLock({Stmt::read(id, decl, arr@src) | read(id, decl, _) <- potentialWrites}, acquireActions);
		return <stmts, potential, env, typesOf, acquireActions, mergeExceptions(exsLhs, exsRhs)>;
	}
	
	//get the variable name
	loc var;
	for(w:read(_, name, _) <- potentialWrites) {
		var = name;
	}
	<changed, env, typesOf> = propagateChanges(target, env, typesOf, dep);
	stmts += addAndLock(changed, acquireActions);
	if(var in volatileFields) 
		stmts += addAndUnlock(stmts, dep, var);
		
	stmts += addAndLock({Stmt::assign(dep, var, id) | id <- getDataDependencyIds(potentialReads)} 
	                  + {Stmt::assign(dep, var, id) | id <- independentValues}
	                  , acquireActions);
	env[var] = {dep};
	potential = addAndLock({Stmt::read(id, var, dep) | read(id, var, _) <- potentialWrites}, acquireActions);
	return <stmts, potential, env, typesOf, acquireActions, mergeExceptions(exsLhs, exsRhs)>;
	
}