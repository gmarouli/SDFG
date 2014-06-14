module lang::sccfg::converter::util::EnvironmentManagement

import IO;
import lang::sccfg::ast::DataFlowLanguage;



data FlowEnvironment = flowEnvironment(map[loc,set[loc]] continueEnv, map[loc,set[loc]] breakEnv, map[loc,set[loc]] retEnv);

map[loc,set[loc]] getContinueEnvironment(flowEnvironment(env, _, _)) = env;
map[loc,set[loc]] getBreakEnvironment(flowEnvironment(_, env, _)) = env;
map[loc,set[loc]] getReturnEnvironment(flowEnvironment(_, _, env)) = env;

map[loc,set[loc]] updateEnvironment(map[loc,set[loc]] env, map[loc,set[loc]] tempEnv){
	for(variable <- tempEnv){
		if(variable in env){
			env[variable] = tempEnv[variable];
		}
	}
	return env;
}

map[loc,set[loc]] mergeNestedEnvironment(map[loc,set[loc]] env, map[loc,set[loc]] nested){
	for(variable <- nested){
		if(variable in env){
			env[variable] = env[variable] + nested[variable];
		}
	}
	return env;
}

map[loc,set[loc]] merge(map[loc,set[loc]] env1, map[loc,set[loc]] env2){
	for(variable <- env2){
		if(variable in env1){
			env1[variable] = env1[variable] + env2[variable];
		}
		else{
			env1[variable] = env2[variable];
		}
	}
	return env1;
}

map[str, map[loc, set[loc]]] mergeExceptions(map[str, map[loc, set[loc]]] exs1, map[str, map[loc, set[loc]]] exs2){
	for(ex <- exs2){
		if(ex in exs1){
			exs1[ex] = merge(exs1[ex], exs2[ex]);
		}
		else{
			exs1[ex] = exs2[ex];
		}
	}
	return exs1;
}

FlowEnvironment mergeBreak(flowEnvironment(contEnv, brEnv, retEnv), map[loc,set[loc]] current)
	= flowEnvironment(contEnv, merge(brEnv, current), retEnv);

FlowEnvironment mergeContinue(flowEnvironment(contEnv, brEnv, retEnv), map[loc,set[loc]] current)
	= flowEnvironment(merge(contEnv, current), brEnv, retEnv);
	
FlowEnvironment mergeReturn(flowEnvironment(contEnv, brEnv, retEnv), map[loc,set[loc]] current)
	= flowEnvironment(contEnv, brEnv, merge(retEnv, current));