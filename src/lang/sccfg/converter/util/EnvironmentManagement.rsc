module lang::sccfg::converter::util::EnvironmentManagement

import IO;
import lang::sccfg::ast::DataFlowLanguage;



data FlowEnvironment = flowEnvironment(map[loc,set[loc]] continueEnv, map[loc,set[loc]] breakEnv);

map[loc,set[loc]] getContinueEnvironment(flowEnvironment(env, _)) = env;
map[loc,set[loc]] getBreakEnvironment(flowEnvironment(_, env)) = env;

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

FlowEnvironment mergeBreak(flowEnvironment(contEnv, brEnv), map[loc,set[loc]] current)
	= flowEnvironment(contEnv, merge(brEnv, current));

FlowEnvironment mergeContinue(flowEnvironment(contEnv, brEnv), map[loc,set[loc]] current)
	= flowEnvironment(merge(contEnv, current), brEnv);