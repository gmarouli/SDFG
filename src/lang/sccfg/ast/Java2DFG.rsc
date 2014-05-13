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

set[Stmt] getStatements(set[Declaration] asts, set[Decl] decls) = {};