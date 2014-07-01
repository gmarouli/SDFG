module lang::sccfg::converter::util::ExceptionManagement

import lang::sccfg::converter::util::EnvironmentManagement;

data ExceptionState = exceptionState(map[loc, set[loc]] env, rel[loc,loc] actions);

ExceptionState emptyExceptionState() = exceptionState((), {});

//Environment
map[loc, set[loc]] getEnvironmentFromException(exceptionState(env, _)) = env;

//Acquire actions
rel[loc,loc] getAcquireActionsFromException(exceptionState(_, acqAc)) = acqAc;

ExceptionState mergeExceptionState(exceptionState(env, actions), exceptionState(newEnv, newActions)){
	exceptionState(merge(env, newEnv), actions + newActions);
}

ExceptionState getExceptionState(map[str, ExceptionState] exs, str exceptionName)
	= <exs[exceptionName], delete(exs, exceptionName)>;