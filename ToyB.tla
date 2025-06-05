-------------------------------- MODULE ToyB --------------------------------
CONSTANT RMs
VARIABLES oncePrepare, onceCommit, onceAbort

Init == 
    /\ oncePrepare == [rm \in RMs |-> FALSE]
    /\ onceCommit  == [rm \in RMs |-> FALSE]
    /\ oceAbort    == [rm \in RMs |-> FALSE]
    
Prepare(rm) ==
    /\ oncePrepare[rm] = TRUE
    /\ UNCHANGED(onceCommit)
    /\ UNCHANGED(onceAbort)
    
Commit(rm) ==
    /\ onceCommit[rm] = TRUE
    /\ UNCHANGED(oncePrepare)
    /\ UNCHANGED(onceAbort)
    
Abort(rm) ==
    /\ onceAbort[rm] = TRUE
    /\ UNCHANGED(oncePrepare)
    /\ UNCHANGED(onceCommit)

=============================================================================
\* Modification History
\* Last modified Thu Jun 05 10:21:06 EDT 2025 by johnnguyen
\* Created Thu Jun 05 10:18:42 EDT 2025 by johnnguyen
