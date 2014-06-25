module lang::sccfg::converter::GatherStmtFromExpressions

import IO;
import Set;
import List;
import String;
import lang::sccfg::ast::DataFlowLanguage;
import lang::java::m3::TypeSymbol;
import lang::java::jdt::m3::AST;
import lang::sccfg::converter::util::ControlFlowHelpers;
import lang::sccfg::converter::util::ContainersManagement;
import lang::sccfg::converter::util::EnvironmentManagement;
import lang::sccfg::converter::Java2DFG;


//The functions are ordered according to the rascal/src/org/rascalImpl/library/lang/java/m3/AST.rsc [last accessed 13/5/2014]

//arrayAccess(Expression array, Expression index)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[str, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m, Expression e:arrayAccess(ar, index), map[loc,set[loc]] env, lrel[loc, loc] locks, set[Stmt] stmts){
	<stmts, indexRead, env, exs> = gatherStmtFromExpressions(m, index, env, locks, stmts);
	stmts = addAndLock(indexRead, locks, stmts);

	
	potential = {Stmt::read(ar@src, ar@decl, id) | id <- getDependencyIds(indexRead)}; //have to find the right read	
	
	return <stmts, potential, env, exs>;
}

//newArray(Type type, list[Expression] dimensions, list[Expression] init)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[str, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m, Expression e:newArray(_, dimensions, init), map[loc,set[loc]] env, lrel[loc, loc] locks, set[Stmt] stmts){
	potential1 = {};
	exs = ();
	for(d <- dimensions){
		<stmts, potential1, env, exsC> = gatherStmtFromExpressions(m, d, env, locks, stmts);
		exs = mergeExceptions(exs,exsC);
	}
	
	<stmts, potential2, env, exsC> = gatherStmtFromExpressions(m, init, env, locks, stmts);
	exs = mergeExceptions(exs,exsC);
	potential = potential1 + potential2;
	stmts = addAndLock(potential, locks, stmts);
		
	loc con = |java+constructor:///array|;
	potential = {create(e@src, con, id) | id <- getDependencyIds(potential)};
	return <stmts, potential, env, exs>;
}

//newArray(Type type, list[Expression] dimensions)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[str, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m, Expression e:newArray(t, dimensions), map[loc,set[loc]] env, lrel[loc, loc] locks, set[Stmt] stmts){
	return gatherStmtFromExpressions(m , Expression::newArray(t, dimensions, Expression::null())[@src=e@src][@typ=e@typ], env, locks, stmts);
}

//arrayInitializer(list[Expression] elements)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[str, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m, Expression e:arrayInitializer(list[Expression] elements), map[loc,set[loc]] env, lrel[loc, loc] locks, set[Stmt] stmts){
	potential = {};
	exs = ();
	for(el <- elements){
		<stmts, potentialC, env, exsC> = gatherStmtFromExpressions(m, el, env, locks, stmts);
		exs = mergeExceptions(exs, exsC);
		potential += potentialC;
	}
	return <stmts, potential, env, exs>;
}

//assignment(Expression lhs, str operator, Expression rhs)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[str, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m, Expression e:assignment(lhs,_,rhs), map[loc,set[loc]] env, lrel[loc, loc] locks, set[Stmt] stmts){
	<stmts, potentialReads, env, exsLhs> = gatherStmtFromExpressions(m, rhs, env, locks, stmts);	
	<stmts, potentialWrites, env, exsRhs> = gatherStmtFromExpressions(m, lhs, env, locks, stmts);
	
	stmts = addAndLock(potentialReads + { Stmt::assign(e@src, var, id) | Stmt:read(_, var, _) <- potentialWrites, id <- getDependencyIds(potentialReads)}, locks, stmts);

	<assigned,_> = takeOneFrom(potentialWrites);
	var = getVarFromStmt(assigned);
	env[var] = {e@src};
	potential = {Stmt::read(lhs@src, var, e@src)};
	
	return <stmts, potential, env, mergeExceptions(exsLhs, exsRhs)>;
}

//cast(Type type, Expression expression)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[str, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m , Expression e:cast(_, exp), map[loc,set[loc]] env, lrel[loc, loc] locks, set[Stmt] stmts){
	return gatherStmtFromExpressions(m, exp, env, locks, stmts);
}

//newObject(Expression expr, Type type, list[Expression] args, Declaration class)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[str, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m , Expression e:newObject(expr, _, args, _), map[loc,set[loc]] env, lrel[loc, loc] locks, set[Stmt] stmts){
	return gatherStmtFromExpressions(m, Expression::newObject(expr, args)[@src = e@src][@decl = e@decl], env, locks, stmts);
}
//newObject(Expression expr, Type type, list[Expression] args)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[str, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m , Expression e:newObject(expr, _, args), map[loc,set[loc]] env, lrel[loc, loc] locks, set[Stmt] stmts){
	return gatherStmtFromExpressions(m, Expression::newObject(expr, args)[@src = e@src][@decl = e@decl], env, locks, stmts);
}

//newObject(Expression expr, list[Expression] args, Declaration class)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[str, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m , Expression e:newObject(expr, args, _), map[loc,set[loc]] env, lrel[loc, loc] locks, set[Stmt] stmts){
	return gatherStmtFromExpressions(m, Expression::newObject(expr, args)[@src=e@src][@decl = emptyId], env, locks, stmts);
}

//newObject(Expression expr, list[Expression] args)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[str, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m , Expression e:newObject(expr, args), map[loc,set[loc]] env, lrel[loc, loc] locks, set[Stmt] stmts){
	potential = {};
	exs = ();
	for(arg <- args){
		<stmts, potential, env, exsC> = gatherStmtFromExpressions(m, arg, env, locks, stmts);
		exs = mergeExceptions(exs, exsC);
	}
	stmts = addAndLock(potential, locks, stmts);
	
	loc con = |java+constructor:///|;
	con.path = e@decl.path ? emptyId;
	potential = {create(e@src, con, id) | id <- getDependencyIds(potential)};

	return <stmts, potential, env, exs>;
}

//qualifiedName(Expression qualifier, Expression expression)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[str, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m , Expression e:qualifiedName(q,exp), map[loc,set[loc]] env, lrel[loc, loc] locks, set[Stmt] stmts){
	<stmts, potential, env, exs> = gatherStmtFromExpressions(m, q, env, locks, stmts);
	stmts = addAndLock(potential, locks, stmts);
	
	<stmts, potentialRead, env, exsR> = gatherStmtFromExpressions(m, exp, env, locks, stmts);
	stmts = addAndLock({read(addr, var, id) | Stmt::read(addr, var, _) <- potentialRead, id <- getDependencyIds(potential)}, locks, stmts);
	return <stmts, potentialRead, env, mergeExceptions(exs, exsR)>;
}

//conditional(Expresion cond, Expression ifB, Expression elseB)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[str, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m, Expression e:conditional(cond,ifB,elseB), map[loc,set[loc]] env, lrel[loc, loc] locks, set[Stmt] stmts){	
	<stmts, potential, env, exs> = gatherStmtFromExpressions(m, cond, env, locks, stmts);
	stmts = addAndLock(potential, locks, stmts);
	
	<stmts, potentialIf, envIf, exsIf> = gatherStmtFromExpressions(m, ifB, env, locks, stmts);				
	<stmts, potentialElse, envElse, exsElse> = gatherStmtFromExpressions(m, elseB, env, locks, stmts);

	env = updateEnvironment(env,envIf);
	env = mergeNestedEnvironment(env,envElse);
	exs = mergeExceptions(exs,exsIf);
	exs = mergeExceptions(exs,exsElse);
	return <stmts, potential + potentialIf + potentialElse, env, exs>;
}

//fieldAccess(bool isSuper, Expression expression, str name)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[str, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m , Expression e:fieldAccess(_,exp,_), map[loc,set[loc]] env, lrel[loc, loc] locks, set[Stmt] stmts){
	<stmts, potential, env, exs> = gatherStmtFromExpressions(m, exp, env, locks, stmts);
	potential = {Stmt::read(e@src, e@decl, writtenBy) | writtenBy <- env[e@decl] ? {emptyId}} + {Stmt::read(e@src, e@decl, dependOn) | dependOn <- getDependencyIds(potential)};	
	return <stmts, potential, env, exs>;
}

//fieldAccess(bool isSuper, str name)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[str, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m , Expression e:fieldAccess(_, _), map[loc,set[loc]] env, lrel[loc, loc] locks, set[Stmt] stmts){
	potential = {Stmt::read(e@src, e@decl, writtenBy) | writtenBy <- env[e@decl] ? {emptyId}};	
	return <stmts, potential, env, ()>;
}

//instanceof(Expression leftside, Type rightSide)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[str, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m , Expression e:\instanceof(lsh,_), map[loc,set[loc]] env, lrel[loc, loc] locks, set[Stmt] stmts){
	<stmts, potential, env, exs> = gatherStmtFromExpressions(m, lhs, env, locks, stmts);
	stmts = addAndLock(potential, locks, stmts);
	return <stmts, {}, env, exs>;
}

//methodCall(bool isSuper, str name, list[Expression] arguments)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[str, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m , Expression e:methodCall(isSuper,name,args), map[loc,set[loc]] env, lrel[loc, loc] locks, set[Stmt] stmts){
	return gatherStmtFromExpressions(m, \methodCall(isSuper, \this(), name, args), env, locks, stmts);
}

//method(bool isSuper, Expression receiver, str name, list[Expression] arguments)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[str, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m , Expression e:methodCall(isSuper, receiver, name, args), map[loc,set[loc]] env, lrel[loc, loc] locks, set[Stmt] stmts){
	set[Stmt] potential = {};
	map[str, map[loc,set[loc]]] exs = ();
	for(arg <- args){
		<stmts, potential, env, exsC> = gatherStmtFromExpressions(m, arg, env, locks, stmts);
		exs = mergeExceptions(exs,exsC);
	}
	println(e);
	stmts = addAndLock(potential + {Stmt::call(e@src, receiver@decl, e@decl, arg) | arg <- getDependencyIds(potential)}, locks, stmts);
	
	for(ex <- exceptions[e@decl] ? {}){
		if(ex in exs){
			exs[ex] = merge(exs[ex],env);
		}
		else{
			exs[ex] = env;
		}
	}
	return <stmts, {}, env, exs>;
}

//variable(str name, int extraDimensions, Expression init)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[str, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m , Expression e:variable(name,_,rhs), map[loc,set[loc]] env, lrel[loc, loc] locks, set[Stmt] stmts){
	<stmts, potential, env, exs> = gatherStmtFromExpressions(m, rhs, env, locks, stmts);
	stmts = addAndLock(potential + {Stmt::assign(e@src, e@decl, id) | id <- getDependencyIds(potential)}, locks, stmts);
	env[e@decl] = {e@src};
	return <stmts, {}, env, exs>;
}

//bracket(Expression exp);
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[str, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m, Expression e:\bracket(exp), map[loc,set[loc]] env, lrel[loc, loc] locks, set[Stmt] stmts){
	return gatherStmtFromExpressions(m, exp, env, locks, stmts);
}

//this()
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[str, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m , Expression e:this(), map[loc,set[loc]] env, lrel[loc, loc] locks, set[Stmt] stmts){
	potential = {Stmt::read(e@src, |java+field:///|+ extractClassName(m@decl)+"/this", emptyId)};
	return <stmts, potential, env, ()>;
}

//this(Expression exp)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[str, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m , Expression e:this(exp), map[loc,set[loc]] env, lrel[loc, loc] locks, set[Stmt] stmts){
	assert false : "Found this with expression in: <e>!";
	return <stmts, {}, env, ()>;
}

//super()
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[str, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m , Expression e:super(), map[loc,set[loc]] env, lrel[loc, loc] locks, set[Stmt] stmts){
	assert false : "Found super in: <e>!";
	return <stmts, {}, env, ()>;
}

//declarationExpression(Declaration d)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[str, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m , Expression e:declarationExpression(d), map[loc,set[loc]] env, lrel[loc, loc] locks, set[Stmt] stmts){
	<stmts, env, exs> = gatherStmtFromStatements(m, declarationStatement(d), env, locks, stmts); 
	return <stmts, {}, env, exs>;
}

//infix(Expression lhs, str operator, Expression rhs, list[Expression] extendedOperands)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[str, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m, Expression e:infix(lhs, operator, rhs, ext), map[loc,set[loc]] env, lrel[loc, loc] locks, set[Stmt] stmts){
	operands = [lhs,rhs] + ext;
	if(operator == "&&" || operator == "||"){
		return shortCircuit(m, operands, env, locks, stmts);
	}
	else{
		potential = {};
		exs = ();
		for(op <- operands){
			<stmts, potentialOp, env, exsOp> = gatherStmtFromExpressions(m, op, env, locks, stmts);
			potential += potentialOp;
			exs = mergeExceptions(exs,exsOp);
		}
		return <stmts, potential, env, exs>;
	}
}

//postfix(Expression operand, str operator)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[str, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m, Expression e:postfix(operand, operator), map[loc,set[loc]] env, lrel[loc, loc] locks, set[Stmt] stmts){
	if(operator == "++" || operator == "--"){
		<stmts, potential, env, exs> = gatherStmtFromExpressions(m, operand, env, locks, stmts);
		stmts = addAndLock(potential + {Stmt::assign(e@src, operand@decl, id) | id <- getDependencyIds(potential)}, locks, stmts);

		potential = {Stmt::read(operand@src, operand@decl, writtenBy) | writtenBy <- env[operand@decl] ? {emptyId}};				
		env[operand@decl] = {e@src};
	
		return <stmts, potential, env, exs>;
	}
	else{
		return gatherStmtFromExpressions(m, operand, env, locks, stmts);
	}
}

//prefix(str operator, Expression operand)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[str, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m, Expression e:prefix(operator, operand), map[loc,set[loc]] env, lrel[loc, loc] locks, set[Stmt] stmts){
	if(operator == "++" || operator == "--"){
		<stmts, potential, env, exs> = gatherStmtFromExpressions(m, operand, env, locks, stmts);
		stmts = addAndLock(potential + {Stmt::assign(e@src, operand@decl, id) | id <- getDependencyIds(potential)}, locks, stmts);
		
		env[operand@decl] = {e@src};
		potential = {Stmt::read(operand@src, operand@decl, e@src)};
		return <stmts, potential, env, exs>;
	}
	else{
		return gatherStmtFromExpressions(m, operand, env, locks, stmts);
	}
}

//simpleName(str name)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[str, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m , Expression e:simpleName(name), map[loc,set[loc]] env, lrel[loc, loc] locks, set[Stmt] stmts){
	potential = {Stmt::read(e@src, e@decl, writtenBy) | writtenBy <- env[e@decl] ? {emptyId}};	
	return <stmts, potential, env, ()>;
}

tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[str, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m , Expression e:\type(simpleType(name)), map[loc,set[loc]] env, lrel[loc, loc] locks, set[Stmt] stmts){
	potential = {Stmt::read(e@src, name@decl+".class", emptyId)};	
	return <stmts, potential, env, ()>;
}

default tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[str, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m, Expression e, map[loc,set[loc]] env, lrel[loc, loc] locks, set[Stmt] stmts){
	return <stmts, {}, env, ()>;
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

set[Stmt] addAndLock(set[Stmt] newStmts, lrel[loc, loc] locks, set[Stmt] stmts){
	for(<idL, l> <- locks){
		newStmts += { Stmt::lock(idL, l, getIdFromStmt(s)) | s <- newStmts}; //every lock needs to be locked by the next ones
	}
	stmts += newStmts;
	return stmts;
}