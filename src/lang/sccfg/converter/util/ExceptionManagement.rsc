module lang::sccfg::converter::util::ExceptionManagement

import lang::sccfg::converter::util::State;
import lang::sccfg::converter::util::EnvironmentManagement;

public map[loc, set[str]] exceptions = ();

map[str, State] mergeExceptions(map[str, State] exs1, map[str, State] exs2){
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

State getExceptionState(map[str, State] exs, str exceptionName)
	= <exs[exceptionName], delete(exs, exceptionName)>;