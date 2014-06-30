module lang::sccfg::converter::util::AcquireActionsManagement

data AcquireActionsPaths = acquireActionsPaths(rel[loc,loc] acqFromContinue, rel[loc,loc] acqFromBreak, rel[loc,loc] acqFromReturn);

AcquireActionsPaths emptyAcquireActionsPaths() = acquireActionsPaths({}, {}, {});

//Continue
rel[loc,loc] getAcquireActionsFromContinue(acquireActionsPaths(acqAc, _, _)) = acqAc;

AcquireActionsPaths initializeAcquireActionsFromContinue(rel[loc,loc] newActions) 
	= acquireActionsPaths(newActions, {}, {});

//Break
rel[loc,loc] getAcquireActionsFromBreak(acquireActionsPaths(_, _, acqAc, _)) = acqAc;

AcquireActionsPaths initializeAcquireActionsFromBreak(rel[loc,loc] newActions) 
	= acquireActionsPaths({}, newActions, {});

//Return
rel[loc,loc] getAcquireActionsFromReturn(acquireActionsPaths(_, _, acqAc)) = acqAc;

AcquireActionsPaths initializeAcquireActionsFromReturn(rel[loc,loc] newActions) 
	= acquireActionsPaths({}, {}, newActions);

//General
AcquireActionsPaths mergeActions(AcquireActionsPaths a:acquireActionsPaths(acqAcCont, acqAcBr, acqAcRet), AcquireActionsPaths t:acquireActionsPaths(acqAcContT, acqAcBrT, acqAcRetT)){
	return acquireActionsPaths(acqAcCont + acqAcContT, acqAcBr + acqAcBrT, acqAcRet + acqAcRetT);
}
