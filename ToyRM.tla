------------------------------- MODULE ToyRM -------------------------------
EXTENDS SharedVariables
VARIABLES rmState

InitToyRM == rmState = [rm \in rmState |-> "working"]

PrepareToyRM(rm) ==
    /\ rmState[rm] = "working"
    /\ rmState' = [rmState EXCEPT ![rm] = "prepared"]

CommitToyRM(rm) ==
    /\ rmState' = [rmState EXCEPT ![rm] = "commit"]
    
AbortToyRM(rm) ==
    /\ rmState' = [rmState EXCEPT ![rm] = "abort"]
    
SilentAbortToyRM(rm) ==
    /\ rmState[rm] = "working"
    /\ rmState' = [rmState EXCEPT ![rm] = "abort"]


=============================================================================
\* Modification History
\* Last modified Thu Jun 05 20:10:26 EDT 2025 by johnnguyen
\* Created Thu Jun 05 20:04:11 EDT 2025 by johnnguyen
