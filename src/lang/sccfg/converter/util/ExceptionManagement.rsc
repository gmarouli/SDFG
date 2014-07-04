module lang::sccfg::converter::util::ExceptionManagement

import lang::sccfg::converter::util::EnvironmentManagement;

data ExceptionState = exceptionState(map[loc, set[loc]] env, rel[loc,loc] actions);

public map[loc, set[str]] exceptions = ();

ExceptionState emptyExceptionState() = exceptionState((), {});

//Environment
map[loc, set[loc]] getEnvironmentFromException(exceptionState(env, _)) = env;

//Acquire actions
rel[loc,loc] getAcquireActionsFromException(exceptionState(_, acqAc)) = acqAc;

ExceptionState mergeExceptionState(exceptionState(env, actions), exceptionState(newEnv, newActions)){
	exceptionState(merge(env, newEnv), actions + newActions);
}

map[str, ExceptionState] mergeExceptions(map[str, ExceptionState] exs1, map[str, ExceptionState] exs2){
	for(ex <- exs2){
		if(ex in exs1){
			exs1[ex] = mergeExceptionState(exs1[ex], exs2[ex]);
		}
		else{
			exs1[ex] = exs2[ex];
		}
	} 
	return exs1;
}

ExceptionState getExceptionState(map[str, ExceptionState] exs, str exceptionName)
	= <exs[exceptionName], delete(exs, exceptionName)>;