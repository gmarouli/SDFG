module lang::sccfg::ast::util::ContainersManagement

import Set;
import List;
import lang::java::jdt::m3::AST;

public set[Declaration] fixCollections(set[Declaration] ast) {
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