-------------------------------- MODULE ToyB --------------------------------
EXTENDS SharedVariables

VARIABLES oncePrepare, onceCommit, onceAbort

InitToyB == 
    /\ oncePrepare = [rm \in RMs |-> FALSE]
    /\ onceCommit  = [rm \in RMs |-> FALSE]
    /\ onceAbort    = [rm \in RMs |-> FALSE]
    
PrepareToyB(rm) ==
    /\ oncePrepare[rm] = TRUE
    /\ UNCHANGED(onceCommit)
    /\ UNCHANGED(onceAbort)
    
CommitToyB(rm) ==
    /\ onceCommit[rm] = TRUE
    /\ UNCHANGED(oncePrepare)
    /\ UNCHANGED(onceAbort)
    
AbortToyB(rm) ==
    /\ onceAbort[rm] = TRUE
    /\ UNCHANGED(oncePrepare)
    /\ UNCHANGED(onceCommit)

=============================================================================
\* Modification History
\* Last modified Thu Jun 05 20:10:14 EDT 2025 by johnnguyen
\* Created Thu Jun 05 20:02:38 EDT 2025 by johnnguyen
