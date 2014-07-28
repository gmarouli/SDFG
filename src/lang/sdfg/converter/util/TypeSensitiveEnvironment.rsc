module lang::sdfg::converter::util::TypeSensitiveEnvironment

import lang::java::m3::TypeSymbol;

import lang::sdfg::ast::SynchronizedDataFlowGraphLanguage;

data TypeSensitiveEnvironment = typeEnv(set[loc] decls, set[loc] dependencies);

TypeSensitiveEnvironment emptyTypeSensitiveEnvironment() = typeEnv({}, {emptyId});

//Merge
map[loc, TypeSensitiveEnvironment] mergeTypesEnvironment(map[loc, TypeSensitiveEnvironment] env1, map[loc, TypeSensitiveEnvironment] env2){
	for(typ <- env2){
		if(typ in env1){
			env1[typ] = merge(env1[typ], env2[typ]);
		}
		else{
			env1[typ] = env2[typ];
		}
	}
	return env1;
}

TypeSensitiveEnvironment merge(TypeSensitiveEnvironment e:typeEnv(decl1, dep1), TypeSensitiveEnvironment e:typeEnv(decl2, dep2))
	= typeEnv(decl1 + decl2, dep1 + dep2);
	
//Update
TypeSensitiveEnvironment setDependency(TypeSensitiveEnvironment t:typeEnv(decl, deps), loc dep)
	= typeEnv(decl, {dep});

map[loc,TypeSensitiveEnvironment] update(map[loc,TypeSensitiveEnvironment] typesOf, loc typ, loc src){
	typesOf[typ] = setDependency(typesOf[typ] ? emptyTypeSensitiveEnvironment(), src);
	return typesOf;
}

map[loc, TypeSensitiveEnvironment] addDeclOfType(map[loc, TypeSensitiveEnvironment] typesOf, loc decl, TypeSymbol c:class(typ, _)){
	typesOf[typ] = addDecl(typesOf[typ] ? emptyTypeSensitiveEnvironment(), decl);
	return typesOf;
}
map[loc, TypeSensitiveEnvironment] addDeclOfType(map[loc, TypeSensitiveEnvironment] typesOf, loc decl, TypeSymbol c:interface(typ, _)){
	typesOf[typ] = addDecl(typesOf[typ] ? emptyTypeSensitiveEnvironment(), decl);
	return typesOf;
}
default map[loc, TypeSensitiveEnvironment] addDeclOfType(map[loc, TypeSensitiveEnvironment] typesOf, loc decl, TypeSymbol t)
	= typesOf;

TypeSensitiveEnvironment addDecl(TypeSensitiveEnvironment t:typeEnv(decls, deps), decl)
	= typeEnv(decls + {decl}, deps);
	
//Getters
set[loc] getDeclsFromTypeEnv(TypeSensitiveEnvironment ts:typeEnv(decls, _)) = decls;

set[loc] getDependenciesFromType(map[loc,TypeSensitiveEnvironment] typesOf, loc typ){
	typesOf[typ] = typesOf[typ] ? emptyTypeSensitiveEnvironment();
	return getDependencies(typesOf[typ]);
}

set[loc] getDependencies(TypeSensitiveEnvironment t:typeEnv(_, deps)) = deps;