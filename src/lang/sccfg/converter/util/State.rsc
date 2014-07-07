module lang::sccfg::converter::util::State

import Map;
import lang::sccfg::converter::util::TypeSensitiveEnvironment;

data State = state(map[loc, set[loc]] env, map[loc,TypeSensitiveEnvironment] typesOf, rel[loc,loc] actions);

State emptyState() = state((), (), {});

//Environment
map[loc, set[loc]] getEnvironment(state(env, _, _)) = env;

//TypeSensitiveEnvironment
map[loc,TypeSensitiveEnvironment] getTypesEnvironment(state(_, typs, _)) = typs;

//Acquire actions
rel[loc,loc] getAcquireActions(state(_, _, acqAc)) = acqAc;

State merge(State s1:state(env1, typesOf1, actions1), State s2:state(env2, typesOf2, actions2))
	= state(merge(env1,env2), mergeTypesEnvironment(typesOf1, typesOf2), actions1 + actions2);
	
bool isEmpty(State s:state(env, typs, actions)) = (isEmpty(env)) && (isEmpty(typs)) && (actions == {});
	
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
