module lang::sccfg::ast::Java2DFG

import IO;
import Set;
import List;
import String;
import lang::sccfg::ast::DataFlowLanguage;
import lang::java::m3::TypeSymbol;
import lang::java::jdt::m3::AST;

Program createDFG(loc project) = createDFG(createAstsFromEclipseProject(project, true));

Program createDFG(set[Declaration] asts) {
	println("Getting decls");
	decls = getDeclarations(asts);
	println("Getting stmts");
	stmts = getStatements(asts,decls);
	return program(decls, stmts);
}

set[Decl] getDeclarations(set[Declaration] asts) 
	= { Decl::attribute(v@decl,(volatile() in f@modifiers)) | /f:field(t,frags) <- asts, v <- frags}
	+ { Decl::method(m@decl, [p@decl | p:parameter(t,_,_) <- params], determineLock(m)) | /m:Declaration::method(_,_, list[Declaration] params, _, _)  <- asts}
	+ { Decl::method(m@decl, [p@decl | p:parameter(t,_,_) <- params], determineLock(m)) | /m:Declaration::method(_,_, list[Declaration] params, _)  <- asts}
	+ { Decl::constructor(c@decl, [p@decl | p:parameter(t,_,_) <- params]) | /c:Declaration::constructor(_, list[Declaration] params, _,_)  <- asts}      
	// add implicit constructor
	+ { Decl::constructor((c@decl)[scheme="java+constructor"] + "<name>()", []) | /c:class(name, _, _, b) <- asts, !(Declaration::constructor(_, _, _, _) <- b)}   
	;
	
private loc determineLock(Declaration method){
	loc lock = unlocked;
	if(synchronized() in method@modifiers){
		if(static() in method@modifiers){
			str lockPath = substring(method@decl.path,0,findLast(method@decl.path,"/")) + ".class";
			lock = lock+lockPath;
		}
		else{
			str lockPath = substring(method@decl.path,0,findLast(method@decl.path,"/")+1) + "this";
			lock = lock+lockPath;
		}
	}
	return lock;
}

set[Stmt] getStatements(set[Declaration] asts, set[Decl] decls) {
	allMethods 
		= { m | /m:Declaration::method(_,_,_,_,_) <- asts}
		+ {Declaration::method(t, n, p, e, empty())[@decl=m@decl] | /m:Declaration::method(Type t,n,p,e) <- asts}
		+ {Declaration::method(simpleType(simpleName(n)), n, p, e, b)[@decl=m@decl] | /m:Declaration::constructor(str n,p,e, b) <- asts}
	;
	
	allMethods = fixCollections(allMethods);
	
	allMethods = visit(allMethods) {
		case declarationExpression(Declaration::class(_)) => Expression::null()
		case declarationExpression(Declaration::class(_,_,_,_)) => Expression::null()
		case declarationExpression(Declaration::enum(_,_,_,_)) => Expression::null()
		
		case declarationStatement(Declaration::class(_)) => empty()
		case declarationStatement(Declaration::class(_,_,_,_)) => empty()
		case declarationStatement(Declaration::enum(_,_,_,_)) => empty()
	};
	
	set[Stmt] result = {};
	for (m:Declaration::method(_, _, parameters, _, b) <- allMethods) {
		//determine lock
		loc lock = unlocked;
		for(Decl::method(id, _, l) <- decls){
			if(id.path == m@decl.path)
				lock = l;
		} 
		//set up environment with parameters
		env = ( p@decl : m@src | p <- parameters);
		//<methodStmts, _> = dealWithStmts(m,()); 
		methodStmts = {};
		//lock statements if synchronized
		if(lock != unlocked){
			methodStmts += {Stmt::lock(src, lock, {getIdFromStmt(s) | s <- methodStmts})};
		}
		result+= methodStmts;
	}	
	
	return result;
}

set[Declaration] fixCollections(set[Declaration] ast) {
	return visit (ast) {
		case oe:methodCall(_, Expression receiver, methodName,	args):  {
			if (isContainerInsert(receiver, methodName)) {
				insert assignment(receiver, "=", correctInsertArg(receiver, methodName, args))
					[@typ = receiver@typ]
					[@src = oe@src];
			}
			else if(isContainerExtract(receiver, methodName)) {
				insert receiver;
			}
		}
	};
}

set[str] containerClasses =  {
	 "/java/util/Map"
	,"/java/util/HashMap"
	,"/java/util/Collection"
	,"/java/util/Set"
	,"/java/util/HashSet"
	,"/java/util/LinkedHashSet"
	,"/java/util/List"
	,"/java/util/ArrayList"
	,"/java/util/LinkedList"
};

map[str, int] insertArgs = (
	 "insert": 0
	, "insertAll": 0
	, "put": 1
	, "putAll": 1
	, "add": 0
	, "addAll": 0
);

Expression correctInsertArg(Expression recv, str name, list[Expression] args) {
	return args[insertArgs[name]];
}


bool isContainerInsert(Expression recv, str name) {
	tp = (recv@typ).decl.path;
	if (tp in containerClasses) {
		return name in insertArgs;
	}
	return false;
}

bool isContainerExtract(Expression recv, str name) {
	tp = (recv@typ).decl.path;
	if (tp in containerClasses) {
		switch (name) {
			case "get": return true;	
			case "iterator": return true;	
			case "toArray": return true;	
			case "entrySet": return true;	
			case "values": return true;	
		}	
	}
	return false;
}