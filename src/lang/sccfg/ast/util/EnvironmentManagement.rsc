module lang::sccfg::ast::util::EnvironmentManagement

import IO;


data Environment = environment(map[loc,set[loc]] env, map[loc,set[loc]] continueEnv, map[loc,set[loc]] breakEnv, map[loc,set[loc]] returnEnv);

map[loc,set[loc]] getCurrentEnvironment(environment(env, _, _, _)) = env;
map[loc,set[loc]] getContinueEnvironment(environment(_, env, _, _)) = env;
map[loc,set[loc]] getBreakEnvironment(environment(_, _, env, _)) = env;
map[loc,set[loc]] getreturnEnvironment(environment(_, _, _, env)) = env;

Environment mergeEnvironments(environment(env1, contEnv1, brEnv1, retEnv1), environment(env2, contEnv2, brEnv2, retEnv2)){
	env = mergeEnvironments(env1, env2);
	contEnv = mergeInBlockEnvironments(contEnv1, contEnv2);
	brEnv = mergeInBlockEnvironments(brEnv1, brEnv2);
	retEnv = mergeInBlockEnvironments(retEnv1, retEnv2);
	return environment(env, contEnv, brEnv, retEnv);
}

map[loc,set[loc]] mergeEnvironments(map[loc,set[loc]] env, map[loc,set[loc]] tempEnv){
	for(variable <- tempEnv){
		if(variable in env){
			env[variable] = env[variable] + tempEnv[variable];
		}
	}
	return env;
}

map[loc,set[loc]] mergeInBlockEnvironments(map[loc,set[loc]] env1, map[loc,set[loc]] env2){
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

set[loc] getVariableDependencies(environment(env, _, _, _), variable){
	return env[variable];
}

Environment setVariableDependencies(e:environment(env, contEnv, brEnv, retEnv), loc variable, set[loc] assignments){
	map[loc, set[loc]] envT = env;
	envT[variable] = assignments;
	return environment(envT, contEnv, brEnv, retEnv);
}

Environment mergeContinue(environment(env, contEnv, brEnv, retEnv))
	= environment(mergeInBlockEnvironments(env, contEnv), contEnv, brEnv, retEnv);

Environment mergeBreak(environment(env, contEnv, brEnv, retEnv)) 
	= environment(mergeInBlockEnvironments(env, brEnv), contEnv, brEnv, retEnv);
	
Environment resetHelpingEnvironment(environment(env, _, _, retEnv), environment(_, contEnv, brEnv, _))
	= environment(env, contEnv, brEnv, retEnv);
	
Environment addToContinueEnvironment(environment(env, contEnv, brEnv, retEnv))
	= environment(env, mergeInBlockEnvironments(env, contEnv), brEnv, retEnv);
			
Environment addToBreakEnvironment(environment(env, contEnv, brEnv, retEnv))
	= environment(env, contEnv, mergeInBlockEnvironments(env, brEnv), retEnv);
	
Environment addToReturnEnvironment(environment(env, contEnv, brEnv, retEnv))
	= environment(env, contEnv, brEnv, mergeInBlockEnvironments(env, retEnv));