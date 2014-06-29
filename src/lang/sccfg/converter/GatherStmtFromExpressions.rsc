module lang::sccfg::converter::GatherStmtFromExpressions

import IO;
import Set;
import List;
import String;
import lang::sccfg::ast::DataFlowLanguage;
import lang::java::m3::TypeSymbol;
import lang::java::jdt::m3::AST;
import lang::sccfg::converter::Java2DFG;
import lang::sccfg::converter::util::Getters;
import lang::sccfg::converter::util::ControlFlowHelpers;
import lang::sccfg::converter::util::ContainersManagement;
import lang::sccfg::converter::util::EnvironmentManagement;


//The functions are ordered according to the rascal/src/org/rascalImpl/library/lang/java/m3/AST.rsc [last accessed 13/5/2014]

//arrayAccess(Expression array, Expression index)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], rel[loc,loc], map[str, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m, Expression e:arrayAccess(ar, index), map[loc,set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	<stmts, indexRead, env, exs> = gatherStmtFromExpressions(m, index, env, stmts);
	stmts += indexRead;
	acquireActions += extractAcquireActions(indexRead);
	
	potential = addAndLock({Stmt::read(ar@src, ar@decl, id) | id <- getDependencyIds(indexRead)}, acquireActions); //have to find the right read	
	
	return <stmts, potential, env, acquireActions, exs>;
}

//newArray(Type type, list[Expression] dimensions, list[Expression] init)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], rel[loc,loc], map[str, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m, Expression e:newArray(_, dimensions, init), map[loc,set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	potential = {};
	exs = ();
	for(d <- dimensions){
		<stmts, potential1, env, exsC> = gatherStmtFromExpressions(m, d, env, volatileFields, acquireActions, stmts);
		exs = mergeExceptions(exs,exsC);
		potential += potential1;
		stmts += potential1;
		acquireActions += extractAcquireActions(potential1, volatileFields);
	}
	
	<stmts, potential2, env, exsC> = gatherStmtFromExpressions(m, init, env, volatileFields, acquireActions, stmts);
	exs = mergeExceptions(exs,exsC);
	stmts += potential2;
	potential += potential2;
	acquireActions += extractAcquireActions(potential2, volatileFields);
	
		
	loc con = |java+constructor:///array|;
	potential = addAndLock({create(e@src, con, id) | id <- getDependencyIds(potential)}, acquireActions);
	return <stmts, potential, env, acquireActions, exs>;
}

//newArray(Type type, list[Expression] dimensions)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], rel[loc,loc], map[str, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m, Expression e:newArray(t, dimensions), map[loc,set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	return gatherStmtFromExpressions(m , Expression::newArray(t, dimensions, Expression::null())[@src=e@src][@typ=e@typ], env, volatileFields, acquireActions, stmts);
}

//arrayInitializer(list[Expression] elements)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], rel[loc,loc], map[str, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m, Expression e:arrayInitializer(list[Expression] elements), map[loc,set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	potential = {};
	exs = ();
	for(el <- elements){
		<stmts, potentialC, env, exsC> = gatherStmtFromExpressions(m, el, env, volatileFields, acquireActions, stmts);
		exs = mergeExceptions(exs, exsC);
		potential += potentialC;
		stmts += potentialC;
		acquireActions += extractAcquireActions(potentialC, volatileFields);
	}
	return <stmts, potential, env, acquireActions, exs>;
}

//assignment(Expression lhs, str operator, Expression rhs)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], rel[loc,loc], map[str, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m, Expression e:assignment(lhs,operator,rhs), map[loc,set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	set[Stmt] potentialWrites = {};
	set[Stmt] potentialReads = {};
	exsRhs = ();
	exsLhs = ();
	if(operator != "="){
		<stmts, potentialWrites, env, acquireActions, exsRhs> = gatherStmtFromExpressions(m, lhs, env, volatileFields, acquireActions, stmts);
		stmts += potentialWrites;
		acquireActions += extractAcquireActions(potentialWrites);
		
		<stmts, potentialReads, env, acquireActions, exsLhs> = gatherStmtFromExpressions(m, rhs, env, volatileFields, acquireActions, stmts);	
		stmts += potentialReads;
		acquireActions += extractAcquireActions(potentialReads);
	}
	else{
		<stmts, potentialReads, env, acquireActions, exsLhs> = gatherStmtFromExpressions(m, rhs, env, volatileFields, acquireActions, stmts);	
		stmts += potentialReads;
		acquireActions += extractAcquireActions(potentialReads, volatileFields);
		
		<stmts, potentialWrites, env, acquireActions, exsRhs> = gatherStmtFromExpressions(m, lhs, env, volatileFields, acquireActions, stmts);
	}
	loc var;
	for(w:read(_, name, _) <- potentialWrites){
		var = name;
	}
	if(var in volatileFields) 
		stmts += addAndUnlock(stmts, lhs@src, var);
	stmts += addAndLock({Stmt::assign(e@src, var, id) | id <- getDependencyIds(potentialReads)}, acquireActions);
	env[var] = {e@src};
	potential = addAndLock({Stmt::read(lhs@src, var, e@src)}, acquireActions);
	
	return <stmts, potential, env, acquireActions, mergeExceptions(exsLhs, exsRhs)>;
}

//cast(Type type, Expression expression)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], rel[loc,loc], map[str, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m , Expression e:cast(_, exp), map[loc,set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	return gatherStmtFromExpressions(m, exp, env, volatileFields, acquireActions, stmts);
}

//newObject(Expression expr, Type type, list[Expression] args, Declaration class)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], rel[loc,loc], map[str, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m , Expression e:newObject(expr, _, args, _), map[loc,set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	return gatherStmtFromExpressions(m, Expression::newObject(expr, args)[@src = e@src][@decl = e@decl], env, volatileFields, acquireActions, stmts);
}
//newObject(Expression expr, Type type, list[Expression] args)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], rel[loc,loc], map[str, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m , Expression e:newObject(expr, _, args), map[loc,set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	return gatherStmtFromExpressions(m, Expression::newObject(expr, args)[@src = e@src][@decl = e@decl], env, volatileFields, acquireActions, stmts);
}

//newObject(Expression expr, list[Expression] args, Declaration class)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], rel[loc,loc], map[str, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m , Expression e:newObject(expr, args, _), map[loc,set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	return gatherStmtFromExpressions(m, Expression::newObject(expr, args)[@src=e@src][@decl = emptyId], env, volatileFields, acquireActions, stmts);
}

//newObject(Expression expr, list[Expression] args)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], rel[loc,loc], map[str, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m , Expression e:newObject(expr, args), map[loc,set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	potential = {};
	exs = ();
	for(arg <- args){
		<stmts, potential, env, acquireActions, exsC> = gatherStmtFromExpressions(m, arg, env, volatileFields, acquireActions, stmts);
		stmts += potential;
		acquireActions += extractAcquireActions(potential);
		exs = mergeExceptions(exs, exsC);
	}
	
	loc con = |java+constructor:///|;
	con.path = e@decl.path ? "";
	potential = addAndLock({create(e@src, con, id) | id <- getDependencyIds(potential)}, acquireActions);

	return <stmts, potential, env, acquireActions, exs>;
}

//qualifiedName(Expression qualifier, Expression expression)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], rel[loc,loc], map[str, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m , Expression e:qualifiedName(q,exp), map[loc,set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	<stmts, potential, env, acquireActions, exs> = gatherStmtFromExpressions(m, q, env, volatileFields, acquireActions, stmts);
	stmts += potential;
	acquireActions += extractAcquireActions(potential);
	
	<stmts, potentialRead, env, acquireActions, exsR> = gatherStmtFromExpressions(m, exp, env, volatileFields, acquireActions, stmts);
	potentialRead += addAndLock({read(addr, var, id) | Stmt::read(addr, var, _) <- potentialRead, id <- getDependencyIds(potential)}, acquireActions);
	return <stmts, potentialRead, env, mergeExceptions(exs, exsR)>;
}

//conditional(Expresion cond, Expression ifB, Expression elseB)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], rel[loc,loc], map[str, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m, Expression e:conditional(cond,ifB,elseB), map[loc,set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){	
	<stmts, potential, env, exs> = gatherStmtFromExpressions(m, cond, env, volatileFields, acquireActions, stmts);
	stmts += potential;
	acquireActions += extractAcquireActions(potential);
	
	<stmts, potential, envIf, exsIf> = gatherStmtFromExpressions(m, ifB, env, volatileFields, acquireActions, stmts);	
	stmts += potential;
	acquireActions += extractAcquireActions(potential);			
	
	<stmts, potential, envElse, exsElse> = gatherStmtFromExpressions(m, elseB, env, volatileFields, acquireActions, stmts);
	stmts += potential;
	acquireActions += extractAcquireActions(potential);

	env = updateEnvironment(env,envIf);
	env = mergeNestedEnvironment(env,envElse);
	exs = mergeExceptions(exs,exsIf);
	exs = mergeExceptions(exs,exsElse);
	return <stmts, {}, env, exs>;
}

//fieldAccess(bool isSuper, Expression expression, str name)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], rel[loc,loc], map[str, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m , Expression e:fieldAccess(_,exp,_), map[loc,set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	<stmts, potential, env, acquireActions, exs> = gatherStmtFromExpressions(m, exp, env, volatileFields, acquireActions, stmts);
	stmts += potential;
	acquireActions += extractAcquireActions(potential);
	potential = addAndLock({Stmt::read(e@src, e@decl, writtenBy) | writtenBy <- env[e@decl] ? {emptyId}} + {Stmt::read(e@src, e@decl, dependOn) | dependOn <- getDependencyIds(potential)}, acquireActions);	
	return <stmts, potential, env, acquireActions, exs>;
}

//fieldAccess(bool isSuper, str name)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], rel[loc,loc], map[str, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m , Expression e:fieldAccess(_, _), map[loc,set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	potential = addAndLock({Stmt::read(e@src, e@decl, writtenBy) | writtenBy <- env[e@decl] ? {emptyId}}, acquireActions);	
	return <stmts, potential, env, acquireActions, ()>;
}

//instanceof(Expression leftside, Type rightSide)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], rel[loc,loc], map[str, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m , Expression e:\instanceof(lsh,_), map[loc,set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	<stmts, potential, env, exs> = gatherStmtFromExpressions(m, lhs, env, stmts);
	stmts += potential;
	acquireActions += extractAcquireActions(potential);
	return <stmts, {}, env, acquireActions, exs>;
}

//methodCall(bool isSuper, str name, list[Expression] arguments)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], rel[loc,loc], map[str, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m , Expression e:methodCall(isSuper,name,args), map[loc,set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	return gatherStmtFromExpressions(m, methodCall(isSuper, \this(), name, args)[@typ = m@typ][@src = m@src][@decl = m@decl], env, volatileFields, acquireActions, stmts);
}

//method(bool isSuper, Expression receiver, str name, list[Expression] arguments)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], rel[loc,loc], map[str, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m , Expression e:methodCall(isSuper, receiver, name, args), map[loc,set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	map[str, map[loc,set[loc]]] exs = ();
	potential = {};
	for(arg <- args){
		<stmts, potential, env, acquireActions, exsC> = gatherStmtFromExpressions(m, arg, env, volatileFields, acquireActions, stmts);
		stmts += potential;
		acquireActions += extractAcquireActions(potential, volatileFields);
		exs = mergeExceptions(exs,exsC);
	}
	loc recDecl;
	if(receiver := this())
		recDecl = |java+class:///|+extractClassName(m@decl)+"/this";
	else
		recDecl = receiver@decl;
	stmts += addAndLock({Stmt::call(e@src, recDecl, e@decl, arg) | arg <- getDependencyIds(potential)}, acquireActions);
	
	for(ex <- exceptions[e@decl] ? {}){
		if(ex in exs){
			exs[ex] = merge(exs[ex],env);
		}
		else{
			exs[ex] = env;
		}
	}
	return <stmts, {}, env, acquireActions, exs>;
}

//variable(str name, int extraDimensions, Expression init)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], rel[loc,loc], map[str, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m , Expression e:variable(name,_,rhs), map[loc,set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	<stmts, potential, env, acquireActions, exs> = gatherStmtFromExpressions(m, rhs, env, volatileFields, acquireActions, stmts);
	stmts += potential;
	acquireActions += extractAcquireActions(potential, volatileFields);
	if(e@decl in volatileFields){
		stmts += addAndUnlock(stmts, e@src, e@decl);
	}
	
	stmts += addAndLock({Stmt::assign(e@src, e@decl, id) | id <- getDependencyIds(potential)}, acquireActions);
	env[e@decl] = {e@src};
	return <stmts, {}, env, acquireActions, exs>;
}

//bracket(Expression exp);
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], rel[loc,loc], map[str, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m, Expression e:\bracket(exp), map[loc,set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	return gatherStmtFromExpressions(m, exp, env, volatileFields, acquireActions, stmts);
}

//this() cannot change so maybe it is not needed here
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], rel[loc,loc], map[str, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m , Expression e:this(), map[loc,set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	//potential = {Stmt::read(e@src, |java+field:///|+ extractClassName(m@decl)+"/this", emptyId)};
	return <stmts, {}, env, acquireActions, ()>;
}

//this(Expression exp)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], rel[loc,loc], map[str, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m , Expression e:this(exp), map[loc,set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	assert false : "Found this with expression in: <e>!";
	return <stmts, {}, env, acquireActions, ()>;
}

//super()
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], rel[loc,loc], map[str, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m , Expression e:super(), map[loc,set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	assert false : "Found super in: <e>!";
	return <stmts, {}, env, acquireActions, ()>;
}

//declarationExpression(Declaration d)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], rel[loc,loc], map[str, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m , Expression e:declarationExpression(d), map[loc,set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	exs = ();
	fenv = emptyFlowEnvironment();
	top-down-break visit(d) {
		case Expression exp : {
			<stmts, _, env, acquireActions, exsE> = gatherStmtFromExpressions(m, exp, env, volatileFields, acquireActions, stmts);
			exs = mergeExceptions(exs, exsE);
		}
	}
	return <stmts, {}, env, acquireActions, exs>;
}

//infix(Expression lhs, str operator, Expression rhs, list[Expression] extendedOperands)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], rel[loc,loc], map[str, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m, Expression e:infix(lhs, operator, rhs, ext), map[loc,set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	operands = [lhs,rhs] + ext;
	if(operator == "&&" || operator == "||"){
		return shortCircuit(m, operands, env, volatileFields, acquireActions, stmts);
	}
	else{
		exs = ();
		dependencies = {};
		for(op <- operands){
			<stmts, potential, env, acquireActions, exsOp> = gatherStmtFromExpressions(m, op, env, volatileFields, acquireActions, stmts);
			stmts += potential;
			dependencies += potential;
			acquireActions += extractAcquireActions(potential, volatileFields);
			exs = mergeExceptions(exs,exsOp);
		}
		//the reads are not potential because there are operations done one them that cannot be statements!
		return <stmts, dependencies, env, acquireActions, exs>;
	}
}

//postfix(Expression operand, str operator)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], rel[loc,loc], map[str, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m, Expression e:postfix(operand, operator), map[loc,set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	if(operator == "++" || operator == "--"){
		<stmts, potential, env, acquireActions, exs> = gatherStmtFromExpressions(m, operand, env,  volatileFields, acquireActions, stmts);
		stmts += potential;
		acquireActions += extractAcquireActions(potential, volatileFields);
		
		if(operand@decl in volatileFields){
			stmts += addAndUnlock(stmts, e@src, operand@decl);
		}
		stmts += addAndLock({Stmt::assign(e@src, operand@decl, id) | id <- getDependencyIds(potential)}, acquireActions);
		
		//potential was already found
		//potential = {Stmt::read(operand@src, operand@decl, writtenBy) | writtenBy <- env[operand@decl] ? {emptyId}};				
		env[operand@decl] = {e@src};
	
		return <stmts, potential, env, acquireActions, exs>;
	}
	else{
		return gatherStmtFromExpressions(m, operand, env, volatileFields, acquireActions, stmts);
	}
}

//prefix(str operator, Expression operand)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], rel[loc,loc], map[str, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m, Expression e:prefix(operator, operand), map[loc,set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	if(operator == "++" || operator == "--"){
		<stmts, potential, env, acquireActions, exs> = gatherStmtFromExpressions(m, operand, env, volatileFields, acquireActions, stmts);
		stmts += potential;
		acquireActions += extractAcquireActions(potential, volatileFields);
		
		if(operand@decl in volatileFields){
			stmts += addAndUnlock(stmts, e@src, operand@decl);
		}
		
		stmts += addAndLock({Stmt::assign(e@src, operand@decl, id) | id <- getDependencyIds(potential)}, acquireActions);
		env[operand@decl] = {e@src};
		
		potential = addAndLock({Stmt::read(operand@src, operand@decl, e@src)}, acquireActions);
		return <stmts, potential, env, acquireActions, exs>;
	}
	else{
		return gatherStmtFromExpressions(m, operand, env, volatileFields, acquireActions, stmts);
	}
}

//simpleName(str name)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], rel[loc,loc], map[str, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m , Expression e:simpleName(name), map[loc,set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	potential = addAndLock({Stmt::read(e@src, e@decl, writtenBy) | writtenBy <- env[e@decl] ? {emptyId}}, acquireActions);	
	return <stmts, potential, env, acquireActions, ()>;
}

//type(simpleType(_)) representing <Object>.class no check for volatile required
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], rel[loc,loc], map[str, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m , Expression e:\type(simpleType(name)), map[loc,set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	potential = addAndLock({Stmt::read(e@src, name@decl+".class", emptyId)}, acquireActions);	
	return <stmts, potential, env, acquireActions, ()>;
}

default tuple[set[Stmt], set[Stmt], map[loc,set[loc]], rel[loc,loc], map[str, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m, Expression e, map[loc,set[loc]] env, set[loc] volatileFields, rel[loc,loc] acquireActions, set[Stmt] stmts){
	return <stmts, {}, env, acquireActions, ()>;
}

set[loc] getDependencyIds(set[Stmt] potential){
	if(potential == {}){
		return {emptyId};
	}
	else{
		return { id | Stmt::read(id, _, _) <- potential}
			+  { id | Stmt::call(id, _, _) <- potential}
			+  { id | Stmt::create(id, _, _) <- potential}
			;	
	}
}

set[Stmt] addAndLock(set[Stmt] newStmts, rel[loc,loc] acquireActions)
	= newStmts + {Stmt::acquireLock(idL, l, getIdFromStmt(s)) | s <- newStmts, <idL, l> <- acquireActions};

set[Stmt] addAndUnlock(set[Stmt] newStmts, loc idL, l){
	return newStmts + {Stmt::releaseLock(idL, l, getIdFromStmt(s)) | s <- newStmts};
}
rel[loc, loc] extractAcquireActions(set[Stmt] potential, set[loc] volFields)
	= { <id, var> |  read(id, var, _) <- potential, var in volFields};