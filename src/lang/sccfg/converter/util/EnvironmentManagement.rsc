module lang::sccfg::converter::util::EnvironmentManagement

import lang::sccfg::converter::util::State;
import lang::sccfg::converter::util::TypeSensitiveEnvironment;

data FlowEnvironment = flowEnvironment(State continueState, State breakState, State retState);

FlowEnvironment emptyFlowEnvironment() = flowEnvironment(emptyState(), emptyState(), emptyState());

FlowEnvironment initializeContinueState(map[loc,set[loc]] env, map[loc,TypeSensitiveEnvironment] typesOf, rel[loc,loc] actions) 
	= flowEnvironment(state(env, typesOf, actions), emptyState(), emptyState());
FlowEnvironment initializeBreakState(map[loc,set[loc]] env, map[loc,TypeSensitiveEnvironment] typesOf, rel[loc,loc] actions) 
	= flowEnvironment(emptyState(), state(env, typesOf, actions), emptyState());
FlowEnvironment initializeReturnState(map[loc,set[loc]] env, map[loc,TypeSensitiveEnvironment] typesOf, rel[loc,loc] actions) 
	= flowEnvironment(emptyState(), emptyState(), state(env, typesOf, actions));
	
FlowEnvironment initializeContinueState(State s) 
	= flowEnvironment(s, emptyState(), emptyState());
FlowEnvironment initializeBreakState(State s) 
	= flowEnvironment(emptyState(), s, emptyState());
FlowEnvironment initializeReturnState(State s) 
	= flowEnvironment(emptyState(), emptyState(), s);

State getContinueState(flowEnvironment(env, _, _)) = env;
State getBreakState(flowEnvironment(_, env, _)) = env;
State getReturnState(flowEnvironment(_, _, env)) = env;

map[loc,set[loc]] updateAll(map[loc,set[loc]] env, set[loc] decls, loc dep){
	for(d <- decls){
		env[d] = {dep}; 
	}
	return env;
}

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

FlowEnvironment mergeFlow(flowEnvironment(envC1, envB1, envR1), flowEnvironment(envC2, envB2, envR2))
	= flowEnvironment(merge(envC1, envC2), merge(envB1, envB2), merge(envR1, envR2)); 
	
FlowEnvironment updateContinue(flowEnvironment(envC, envB, envR), State s)
	= flowEnvironment(s, envB, envR); 

FlowEnvironment updateBreak(flowEnvironment(envC, envB, envR), State s)
	= flowEnvironment(envC, s, envR); 

FlowEnvironment updateReturn(flowEnvironment(envC, envB, envR), State s)
	= flowEnvironment(envC, envB, s); 

FlowEnvironment mergeBreak(flowEnvironment(contEnv, brEnv, retEnv), map[loc,set[loc]] current)
	= flowEnvironment(contEnv, merge(brEnv, current), retEnv);

FlowEnvironment mergeContinue(flowEnvironment(contEnv, brEnv, retEnv), map[loc,set[loc]] current)
	= flowEnvironment(merge(contEnv, current), brEnv, retEnv);
	
FlowEnvironment mergeReturn(flowEnvironment(contEnv, brEnv, retEnv), map[loc,set[loc]] current)
	= flowEnvironment(contEnv, brEnv, merge(retEnv, current));