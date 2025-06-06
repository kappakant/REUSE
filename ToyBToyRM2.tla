----------------------------- MODULE ToyBToyRM2 -----------------------------
\* everything all in one file, just for proof of concept
CONSTANT RMs
          \* ToyB
VARIABLES oncePrepare, onceCommit, onceAbort, rmState
          
varsToyRM||ToyB ==
    <<rmState, oncePrepare, onceCommit, onceAbort>>

Prepare(rm) ==
    \* ToyB
    /\ oncePrepare[rm] = TRUE
    /\ UNCHANGED(onceCommit)
    /\ UNCHANGED(onceAbort)
    \* ToyRM
    /\ rmState[rm] = "working"
    /\ rmState' = [rmState EXCEPT ![rm] = "prepared"]

Commit(rm) ==
    /\ onceCommit[rm] = TRUE
    /\ UNCHANGED(oncePrepare)
    /\ UNCHANGED(onceAbort)
    
    /\ rmState' = [rmState EXCEPT ![rm] = "commit"]
    
Abort(rm) ==
    /\ onceAbort[rm] = TRUE
    /\ UNCHANGED(oncePrepare)
    /\ UNCHANGED(onceCommit)
    
    /\ rmState' = [rmState EXCEPT ![rm] = "abort"]
    (***********************************************************************
SilentAbort(rm) ==
    \* Only ToyRM
    /\ rmState[rm] = "working"
    /\ rmState' = [rmState EXCEPT ![rm] = "abort"]
     ***********************************************************************)

 
 Consistent == \forall r1, r2 \in RMs: ~(rmState[r1] = "abort" /\ rmState[r2] = "commit")
 
Irm == 
    /\ Consistent
    /\ \forall r \in RMs: onceCommit[r] <=> rmState[r] = "commit"
    /\ \forall r \in RMs: oncePrepare[r] => rmState[r] # "working"
    /\ \forall r \in RMs: (oncePrepare[r] /\ rmState[r] = "abort") => onceAbort[r]

\* Init for ToyRM||ToyB ==
InitToyRMToyB ==
    \* ToyRM
    /\ rmState = [rm \in rmState |-> "working"]
    \* ToyB
    /\ oncePrepare  = [rm \in RMs |-> FALSE]
    /\ onceCommit   = [rm \in RMs |-> FALSE]
    /\ onceAbort    = [rm \in RMs |-> FALSE]

NextToyRMToyB ==
    \exists rm \in RMs:
        \/ Prepare(rm)
        \/ Commit(rm)
        \/ Abort(rm)
        \*\/ SilentAbort(rm)

\* Testing that candidate inductive invariant is indeed, inductive and invariant. Also checking safety.
THEOREM IrmInitialization == 
    InitToyRMToyB => Irm
    <1> SUFFICES ASSUME InitToyRMToyB
                 PROVE Irm
                 OBVIOUS
    <1>. QED
    
\*THEOREM IrmInduction ==
\*    Irm /\ NextToyRMToyB /\ ToyR /\ ToyR' => Irm'
    
\*THEOREM IrmSafety == 
\*    Irm => Consistent
=============================================================================
\* Modification History
\* Last modified Thu Jun 05 19:38:08 EDT 2025 by johnnguyen
\* Created Thu Jun 05 19:10:40 EDT 2025 by johnnguyen
