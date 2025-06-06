----------------------------- MODULE ToyRMToyB -----------------------------
EXTENDS ToyB, ToyRM

ToyR == 
    /\ (\E r \in RMs: onceCommit[r]) => (\A r \in RMs: oncePrepare[r]))
    /\ (\E r \in RMs: onceAbort[r])  => (\A r \in RMs: ~onceCommit[r]))

Consistent == \A r1, r2 \in RMs: ~(rmState[r1] = "commit" /\ rmState[r2] = "abort")

varsToyRMToyB ==
    <<rmState, 
    oncePrepare, onceCommit, onceAbort>>

\* Init for ToyRM||ToyB ==
InitToyRMToyB ==
    \* ToyRM
    /\ rmState = [rm \in rmState |-> "working"]
    \* ToyB
    /\ oncePrepare = [rm \in RMs |-> FALSE]
    /\ onceCommit  = [rm \in RMs |-> FALSE]
    /\ onceAbort   = [rm \in RMs |-> FALSE]



\* Testing that candidate inductive invariant is indeed, inductive and invariant. Also checking safety.

=============================================================================
\* Modification History
\* Last modified Fri Jun 06 10:15:13 EDT 2025 by johnnguyen
\* Created Thu Jun 05 20:05:41 EDT 2025 by johnnguyen
