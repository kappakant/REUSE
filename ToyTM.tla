------------------------------- MODULE ToyTM -------------------------------
CONSTANT RMs
VARIABLES tmState, tmPrepared

Init == 
    /\ tmState = "init"
    /\ tmPrepared = {}
    
Prepare(rm) ==
    /\ tmState = "init"
    /\ tmPrepared' = tmPrepared \cup {rm}
    /\ UNCHANGED(tmState)
    
Commit(rm) ==
    /\ tmState \in {"init", "commit"}
    /\ tmPrepared = RMs
    /\ tmState' = "commit"
    /\ UNCHANGED(tmPrepared)
    
Abort(rm) ==
    /\ tmState \in {"init", "abort"}
    /\ tmState' = "abort"
    /\ UNCHANGED(tmPrepared)

=============================================================================
\* Modification History
\* Last modified Thu Jun 05 17:12:48 EDT 2025 by johnnguyen
\* Created Wed Jun 04 19:11:12 EDT 2025 by johnnguyen
