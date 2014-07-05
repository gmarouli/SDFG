module lang::sccfg::converter::util::AcquireActionsManagement

data AcquireActionsPaths = acquireActionsPaths(lrel[loc,loc] acqFromContinue, lrel[loc,loc] acqFromBreak, lrel[loc,loc] acqFromReturn);

AcquireActionsPaths emptyAcquireActionsPaths() = acquireActionsPaths([], [], []);

//Continue
lrel[loc,loc] getAcquireActionsFromContinue(acquireActionsPaths(acqAc, _, _)) = acqAc;
AcquireActionsPaths addToActionsFromContinue(acquireActionsPaths(acqCont, acqBr, acqRet), newActions)
	= acquireActionsPaths(acqCont + newActions, acqBr, acqRet);

AcquireActionsPaths initializeAcquireActionsFromContinue(lrel[loc,loc] newActions) 
	= acquireActionsPaths(newActions, [], []);

//Break
lrel[loc,loc] getAcquireActionsFromBreak(acquireActionsPaths(_, _, acqAc, _)) = acqAc;
AcquireActionsPaths addToActionsFromBreak(acquireActionsPaths(acqCont, acqBr, acqRet), newActions)
	= acquireActionsPaths(acqCont, acqBr + newActions, acqRet);

AcquireActionsPaths initializeAcquireActionsFromBreak(lrel[loc,loc] newActions) 
	= acquireActionsPaths([], newActions, []);

//Return
lrel[loc,loc] getAcquireActionsFromReturn(acquireActionsPaths(_, _, acqAc)) = acqAc;
AcquireActionsPaths addToActionsFromReturn(acquireActionsPaths(acqCont, acqBr, acqRet), newActions)
	= acquireActionsPaths(acqCont, acqBr, acqRet + newActions);

AcquireActionsPaths initializeAcquireActionsFromReturn(lrel[loc,loc] newActions) 
	= acquireActionsPaths([], [], newActions);

//General
AcquireActionsPaths mergeActions(AcquireActionsPaths a:acquireActionsPaths(acqAcCont, acqAcBr, acqAcRet), AcquireActionsPaths t:acquireActionsPaths(acqAcContT, acqAcBrT, acqAcRetT)){
	return acquireActionsPaths(acqAcCont + acqAcContT, acqAcBr + acqAcBrT, acqAcRet + acqAcRetT);
}
