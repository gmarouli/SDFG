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
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[loc, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m, Expression e:arrayAccess(ar, index), map[loc,set[loc]] env, map[loc, map[loc,set[loc]]] exs, set[Stmt] stmts){
	<stmts, indexRead, env, exs> = gatherStmtFromExpressions(m, index, env, exs, stmts);
	stmts += indexRead;
	
	potential = {Stmt::read(ar@src, ar@decl, id) | id <- getDependencyIds(indexRead)}; //have to find the right read	
	
	return <stmts, potential, env, exs>;
}

//newArray(Type type, list[Expression] dimensions, list[Expression] init)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[loc, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m, Expression e:newArray(_, dimensions, init), map[loc,set[loc]] env, map[loc, map[loc,set[loc]]] exs, set[Stmt] stmts){
	potential1 = {};
	for(d <- dimensions){
		<stmts, potential1, env, exs> = gatherStmtFromExpressions(m, d, env, exs, stmts);
		stmts += potential1;
	}
	
	<stmts, potential2, env, exs> = gatherStmtFromExpressions(m, init, env, exs, stmts);
	stmts += potential2;
	potential = potential1 + potential2;
		
	loc con = |java+constructor:///array|;
	potential = {create(e@src, con, id) | id <- getDependencyIds(potential)};
	return <stmts, potential, env, exs>;
}

//newArray(Type type, list[Expression] dimensions)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[loc, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m, Expression e:newArray(t, dimensions), map[loc,set[loc]] env, map[loc, map[loc,set[loc]]] exs, set[Stmt] stmts){
	return gatherStmtFromExpressions(m , Expression::newArray(t, dimensions, Expression::null())[@src=e@src][@typ=e@typ], env, exs, stmts);
}

//arrayInitializer(list[Expression] elements)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[loc, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m, Expression e:arrayInitializer(list[Expression] elements), map[loc,set[loc]] env, map[loc, map[loc,set[loc]]] exs, set[Stmt] stmts){
	potential = {};
	for(el <- elements){
		<stmts, potential, env, exs> = gatherStmtFromExpressions(m, el, env, exs, stmts);
		stmts += potential;
	}
	return <stmts, potential, env, exs>;
}

//assignment(Expression lhs, str operator, Expression rhs)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[loc, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m, Expression e:assignment(lhs,_,rhs), map[loc,set[loc]] env, map[loc, map[loc,set[loc]]] exs, set[Stmt] stmts){
	<stmts, potentialReads, env, exs> = gatherStmtFromExpressions(m, rhs, env, exs, stmts);
	stmts += potentialReads;
	
	<stmts, potentialWrites, env, exs> = gatherStmtFromExpressions(m, lhs, env, exs, stmts);
	stmts += { Stmt::assign(e@src, var, id) | Stmt:read(_, var, _) <- potentialWrites, id <- getDependencyIds(potentialReads)};
	
	<assigned,_> = takeOneFrom(potentialWrites);
	var = getVarFromStmt(assigned);
	env[var] = {e@src};
	potential = {Stmt::read(lhs@src, var, e@src)};
	
	return <stmts, potential, env, exs>;
}

//cast(Type type, Expression expression)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[loc, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m , Expression e:cast(_, exp), map[loc,set[loc]] env, map[loc, map[loc,set[loc]]] exs, set[Stmt] stmts){
	return gatherStmtFromExpressions(m, exp, env, exs, stmts);
}

//newObject(Expression expr, Type type, list[Expression] args, Declaration class)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[loc, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m , Expression e:newObject(expr, _, args, _), map[loc,set[loc]] env, map[loc, map[loc,set[loc]]] exs, set[Stmt] stmts){
	return gatherStmtFromExpressions(m, Expression::newObject(expr, args)[@src = e@src][@decl = e@decl], env, exs, stmts);
}
//newObject(Expression expr, Type type, list[Expression] args)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[loc, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m , Expression e:newObject(expr, _, args), map[loc,set[loc]] env, map[loc, map[loc,set[loc]]] exs, set[Stmt] stmts){
	return gatherStmtFromExpressions(m, Expression::newObject(expr, args)[@src = e@src][@decl = e@decl], env, exs, stmts);
}

//newObject(Expression expr, list[Expression] args, Declaration class)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[loc, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m , Expression e:newObject(expr, args, _), map[loc,set[loc]] env, map[loc, map[loc,set[loc]]] exs, set[Stmt] stmts){
	return gatherStmtFromExpressions(m, Expression::newObject(expr, args)[@src=e@src][@decl = emptyId], env, exs, stmts);
}

//newObject(Expression expr, list[Expression] args)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[loc, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m , Expression e:newObject(expr, args), map[loc,set[loc]] env, map[loc, map[loc,set[loc]]] exs, set[Stmt] stmts){
	potential = {};
	for(arg <- args){
		<stmts, potential, env, exs> = gatherStmtFromExpressions(m, arg, env, exs, stmts);
		stmts += potential;
	}
	loc con = |java+constructor:///|;
	con.path = e@decl.path ? emptyId;
	potential = {create(e@src, con, id) | id <- getDependencyIds(potential)};

	return <stmts, potential, env, exs>;
}

//qualifiedName(Expression qualifier, Expression expression)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[loc, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m , Expression e:qualifiedName(q,exp), map[loc,set[loc]] env, map[loc, map[loc,set[loc]]] exs, set[Stmt] stmts){
	assert false : "Found qualified name in: <e>!";
	return <stmts, {}, env, exs>;
}

//conditional(Expresion cond, Expression ifB, Expression elseB)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[loc, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m, Expression e:conditional(cond,ifB,elseB), map[loc,set[loc]] env, map[loc, map[loc,set[loc]]] exs, set[Stmt] stmts){	
	<stmts, potential, env, exs> = gatherStmtFromExpressions(m, cond, env, exs, stmts);
	stmts += potential;
	
	<stmts, potentialIf, envIf, exs> = gatherStmtFromExpressions(m, ifBranch, env, exs, stmts);				
	<stmts, potentialElse, envElse, exs> = gatherStmtFromExpressions(m, elseBranch, env, exs, stmts);

	env = updateEnvironment(env,envIf);
	env = mergeNestedEnvironment(env,envElse);
	return <stmts, potentialIf + potentialElse, env, exs>;
}

//fieldAccess(bool isSuper, Expression expression, str name)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[loc, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m , Expression e:fieldAccess(_,exp,_), map[loc,set[loc]] env, map[loc, map[loc,set[loc]]] exs, set[Stmt] stmts){
	<stmts, potential, env, exs> = gatherStmtFromExpressions(m, exp, env, exs, stmts);
	potential = {Stmt::read(e@src, e@decl, writtenBy) | writtenBy <- env[e@decl] ? {emptyId}} + {Stmt::read(e@src, e@decl, dependOn) | dependOn <- getDependencyIds(potential)};	
	return <stmts, potential, env, exs>;
}

//fieldAccess(bool isSuper, str name)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[loc, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m , Expression e:fieldAccess(_, _), map[loc,set[loc]] env, map[loc, map[loc,set[loc]]] exs, set[Stmt] stmts){
	potential = {Stmt::read(e@src, e@decl, writtenBy) | writtenBy <- env[e@decl] ? {emptyId}};	
	return <stmts, potential, env, exs>;
}

//instanceof(Expression leftside, Type rightSide)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[loc, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m , Expression e:\instanceof(lsh,_), map[loc,set[loc]] env, map[loc, map[loc,set[loc]]] exs, set[Stmt] stmts){
	<stmts, potential, env, exs> = gatherStmtFromExpressions(m, lhs, env, exs, stmts);
	return <stmts+potential, {}, env, exs>;
}

//methodCall(bool isSuper, str name, list[Expression] arguments)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[loc, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m , Expression e:methodCall(isSuper,name,args), map[loc,set[loc]] env, map[loc, map[loc,set[loc]]] exs, set[Stmt] stmts){
	return gatherStmtFromExpressions(m, \methodCall(isSuper, \this(), name, args), env, exs, stmts);
}

//method(bool isSuper, Expression receiver, str name, list[Expression] arguments)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[loc, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m , Expression e:methodCall(isSuper, receiver, name, args), map[loc,set[loc]] env, map[loc, map[loc,set[loc]]] exs, set[Stmt] stmts){
	for(arg <- args){
		<stmts, potential, env, exs> = gatherStmtFromExpressions(m, arg, env, exs, stmts);
		stmts += potential;
	}
	stmts+={Stmt::call(e@src, receiver@decl, e@decl, arg) | arg <- getDependencyIds(potential)};	

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
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[loc, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m , Expression e:variable(name,_,rhs), map[loc,set[loc]] env, map[loc, map[loc,set[loc]]] exs, set[Stmt] stmts){
	<stmts, potential, env, exs> = gatherStmtFromExpressions(m, rhs, env, exs, stmts);
	stmts += potential;
	stmts += {Stmt::assign(e@src, e@decl, id) | id <- getDependencyIds(potential)};
	env[e@decl] = {e@src};
	return <stmts, {}, env, exs>;
}

//variable(str name, int extraDimensions)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[loc, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m , Expression e:variable(name,_), map[loc,set[loc]] env, map[loc, map[loc,set[loc]]] exs, set[Stmt] stmts){
	return <stmts, {}, env, exs>;
}

//bracket(Expression exp);
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[loc, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m, Expression e:\bracket(exp), map[loc,set[loc]] env, map[loc, map[loc,set[loc]]] exs, set[Stmt] stmts){
	return gatherStmtFromExpressions(m, exp, env, exs, stmts);
}

//this()
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[loc, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m , Expression e:this(), map[loc,set[loc]] env, map[loc, map[loc,set[loc]]] exs, set[Stmt] stmts){
	potential = {Stmt::read(e@src, |java+field:///|+ extractClassName(m@decl)+"/this", emptyId)};
	return <stmts, potential, env, exs>;
}

//this(Expression exp)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[loc, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m , Expression e:this(exp), map[loc,set[loc]] env, map[loc, map[loc,set[loc]]] exs, set[Stmt] stmts){
	assert false : "Found this with expression in: <e>!";
	return <stmts, {}, env, exs>;
}

//super()
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[loc, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m , Expression e:super(), map[loc,set[loc]] env, map[loc, map[loc,set[loc]]] exs, set[Stmt] stmts){
	assert false : "Found super in: <e>!";
	return <stmts, {}, env, exs>;
}

//declarationExpression(Declaration d)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[loc, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m , Expression e:declarationExpression(d), map[loc,set[loc]] env, map[loc, map[loc,set[loc]]] exs, set[Stmt] stmts){
	return visitStatements(m, declarationStatement(d), env, exs, stmts);
}

//infix(Expression lhs, str operator, Expression rhs, list[Expression] extendedOperands)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[loc, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m, Expression e:infix(lhs, operator, rhs, ext), map[loc,set[loc]] env, map[loc, map[loc,set[loc]]] exs, set[Stmt] stmts){
	if(ext!=[]){
		assert false : "Found extended operands! <ext>";
	}
	if(operator == "&&" || operator == "||"){
		return shortCircuit(m, lhs, rhs, env, exs, stmts);
	}
	else{
		<stmtsLhs, potentialLhs, env, exs> = gatherStmtFromExpressions(m, lhs, env, exs, stmts);
		<stmtsRhs, potentialRhs, env, exs> = gatherStmtFromExpressions(m, rhs, env, exs, stmts);
		 
		return <stmtsLhs + stmtsRhs, potentialLhs + potentialRhs, env, exs>;
	}
}

//postfix(Expression operand, str operator)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[loc, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m, Expression e:postfix(operand, operator), map[loc,set[loc]] env, map[loc, map[loc,set[loc]]] exs, set[Stmt] stmts){
	if(operator == "++" || operator == "--"){
		<stmts, potential, env, exs> = gatherStmtFromExpressions(m, operand, env, exs, stmts);
		stmts += potential;
		stmts += {Stmt::assign(e@src, operand@decl, id) | id <- getDependencyIds(potential)};
	
		potential = {Stmt::read(operand@src, operand@decl, writtenBy) | writtenBy <- env[operand@decl] ? {emptyId}};				
		env[operand@decl] = {e@src};
	
		return <stmts, potential, env, exs>;
	}
	else{
		return gatherStmtFromExpressions(m, operand, env, exs, stmts);
	}
}

//prefix(str operator, Expression operand)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[loc, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m, Expression e:postfix(operand, operator), map[loc,set[loc]] env, map[loc, map[loc,set[loc]]] exs, set[Stmt] stmts){
	if(operator == "++" || operator == "--"){
		<stmts, potential, env, exs> = gatherStmtFromExpressions(m, operand, env, exs, stmts);
		stmts += potential;
		stmts += {Stmt::assign(e@src, operand@decl, id) | id <- getDependencyIds(potential)};
	
		env[operand@decl] = {e@src};
		potential = {Stmt::read(operand@src, operand@decl, e@src)};
		
		return <stmts, potential, env, exs>;
	}
	else{
		return gatherStmtFromExpressions(m, operand, env, exs, stmts);
	}
}

//simpleName(str name)
tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[loc, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m , Expression e:simpleName(name), map[loc,set[loc]] env, map[loc, map[loc,set[loc]]] exs, set[Stmt] stmts){
	potential = {Stmt::read(e@src, e@decl, writtenBy) | writtenBy <- env[e@decl] ? {emptyId}};	
	return <stmts, potential, env, exs>;
}

default tuple[set[Stmt], set[Stmt], map[loc,set[loc]], map[loc, map[loc,set[loc]]]] gatherStmtFromExpressions(Declaration m, Expression e, map[loc,set[loc]] env, map[loc, map[loc,set[loc]]] exs, set[Stmt] stmts){
	return <stmts, {}, env, exs>;
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