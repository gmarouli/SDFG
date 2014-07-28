module lang::sdfg::converter::util::ExceptionManagement

import Map; 

import lang::sdfg::converter::util::State;
import lang::sdfg::converter::util::EnvironmentManagement;

public map[loc, set[str]] exceptions = ();

map[str, State] mergeExceptions(map[str, State] exs1, map[str, State] exs2){
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

tuple[State, map[str, State]]  getAndRemoveState(map[str, State] exs, str exceptionName)
	= <exs[exceptionName] ? emptyState(), delete(exs, exceptionName)>;