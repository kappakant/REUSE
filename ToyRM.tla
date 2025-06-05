------------------------------- MODULE ToyRM -------------------------------
CONSTANT RMs
VARIABLES rmState

Init == rmState = [rm \in rmState |-> "working"]

Prepare(rm) ==
    /\ rmState[rm] = "working"
    /\ rmState' = [rmState EXCEPT ![rm] = "prepared"]

Commit(rm) ==
    /\ rmState' = [rmState EXCEPT ![rm] = "commit"]
    
Abort(rm) ==
    /\ rmState' = [rmState EXCEPT ![rm] = "abort"]
    
SilentAbort(rm) ==
    /\ rmState[rm] = "working"
    /\ rmState' = [rmState EXCEPT ![rm] = "abort"]

=============================================================================
\* Modification History
\* Last modified Wed Jun 04 20:06:47 EDT 2025 by johnnguyen
\* Created Wed Jun 04 19:11:02 EDT 2025 by johnnguyen
