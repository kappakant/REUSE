---------------------------- MODULE ToyB||ToyTM ----------------------------
EXTENDS ToyB, ToyTM

ToyR == 
    /\ (\exists r \in RMs: onceCommit[r]) => (\forall r \in RMs: oncePrepare[r])
    /\ (\exists r \in RMs: onceAbort[r])  => (\forall r \in RMs: ~onceCommit[r])

\* Irm \vDash <ToyR>ToyRM||ToyB<Consistent>
\* Test this by checking the three conditions:
\* (1) Init /\ ToyR => Irm
\* (2) Irm /\ Next /\ ToyR /\ ToyR' => Irm'
\* (3) Irm => Consistent
 
Irm == 
    /\ Consistent
    /\ \forall r \in RMs: onceCommit[r] <=> rmState[r] = "commit"
    /\ \forall r \in RMs: oncePrepare[r] => rmState[r] # "working"
    /\ \forall r \in RMs: (oncrePrepare[r] /\ rmState[r] = "abort") => onceAbort[r]

varsToyRM||ToyB ==
    (rmState, 
    oncePrepare, onceCommit, onceAbort)

\* Init for ToyRM||ToyB ==
InitToyRM||ToyB ==
    \* ToyRM
    /\ rmState = [rm \in rmState |-> "working"]
    \* ToyB
    /\ oncePrepare == [rm \in RMs |-> FALSE]
    /\ onceCommit  == [rm \in RMs |-> FALSE]
    /\ oceAbort    == [rm \in RMs |-> FALSE]

NextToyRM||ToyB ==
    \exists rm \in RMs:
        \/ Prepare(rm)
        \/ Commit(rm)
        \/ Abort(rm)
        \/ SilentAbort(rm)

\* Testing that candidate inductive invariant is indeed, inductive and invariant. Also checking safety.
THEOREM IrmInitialization == 
    InitToyRM||ToyB /\ ToyR => Irm
    
THEOREM IrmInduction ==
    Irm /\ NextToyRM||ToyB /\ ToyR /\ ToyR' => Irm'
    
THEOREM IrmSafety == 
    Irm => Consistent
=============================================================================
\* Modification History
\* Last modified Thu Jun 05 17:37:51 EDT 2025 by johnnguyen
\* Created Thu Jun 05 17:13:22 EDT 2025 by johnnguyen
