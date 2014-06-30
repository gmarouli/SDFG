module lang::sccfg::converter::util::AcquireActionsManagement

import IO;
import lang::sccfg::ast::DataFlowLanguage;



data AcquireActionsPaths = acquireActionsPaths(map[str,rel[loc,loc]] exs, rel[loc,loc] acqFromContinue, rel[loc,loc] acqFromBreak, rel[loc,loc] acqFromReturn);

AcquireActionsPaths emptyAcquireActionsPaths() = acquireActionsPaths((), {}, {}, {});

//Continue
rel[loc,loc] getAcquireActionsFromContinue(acquireActionsPaths(_, acqAc, _, _)) = acqAc;

AcquireActionsPaths initializeAcquireActionsFromContinue(rel[loc,loc] newActions) 
	= acquireActionsPaths((), newActions, {}, {});

//Break
rel[loc,loc] getAcquireActionsFromBreak(acquireActionsPaths(_, _, acqAc, _)) = acqAc;

AcquireActionsPaths initializeAcquireActionsFromBreak(rel[loc,loc] newActions) 
	= acquireActionsPaths((), {}, newActions, {});

//Return
rel[loc,loc] getAcquireActionsFromReturn(acquireActionsPaths(_, _, _, acqAc)) = acqAc;

AcquireActionsPaths initializeAcquireActionsFromReturn(rel[loc,loc] newActions) 
	= acquireActionsPaths((), {}, {}, newActions);

//Exceptions
AcquireActionsPaths initializeAcquireActionsFromException(rel[loc,loc] newActions){
	map[str, rel[loc,loc]] exs = ();
	exs[name] = newActions;
	return acquireActionsPaths(exs, {}, {}, {});
}

rel[loc,loc] getAcquireActionsFromException(acquireActionsPaths(exs, _, _, _), str name) = exs[name] ? {};

AcquireActionsPaths mergeActions(AcquireActionsPaths a:acquireActionsPaths(exs, acqAcCont, acqAcBr, acqAcRet), AcquireActionsPaths t:acquireActionsPaths(exsT, acqAcContT, acqAcBrT, acqAcRetT)){
	return acquireActionsPaths(mergeActionsFromExceptions(exs, exsT), acqAcCont + acqAcContT, acqAcBr + acqAcBrT, acqAcRet + acqAcRetT);
}

map[str, rel[loc,loc]] mergeActions(map[str, rel[loc,loc]] exs1, map[str, rel[loc,loc]] exs2){
	for(ex <- exs2){
		if(ex in exs1){
			exs1[ex] = exs1[ex] + exs2[ex];
		}
		else{
			exs1[ex] = exs2[ex];
		}
	}
	return exs1;
}