----------------------------- MODULE ToyBToyRM -----------------------------
CONSTANT RMs

ToyB  == INSTANCE ToyB WITH RMs <- RMs
ToyRM == INSTANCE ToyRM WITH RMs <- RMs

ToyR == 
    /\ (\exists r \in RMs: ToyB!onceCommit[r]) => (\forall r \in RMs: ToyB!oncePrepare[r])
    /\ (\exists r \in RMs: ToyB!onceAbort[r])  => (\forall r \in RMs: ~ToyB!onceCommit[r])

\* Irm \vDash <ToyR>ToyRM||ToyB<Consistent>
\* Test this by checking the three conditions:
\* (1) Init /\ ToyR => Irm
\* (2) Irm /\ Next /\ ToyR /\ ToyR' => Irm'
\* (3) Irm => Consistent
 
Irm == 
    /\ ToyRM!Consistent
    /\ \forall r \in RMs: ToyB!onceCommit[r] <=> ToyRM!rmState[r] = "commit"
    /\ \forall r \in RMs: ToyB!oncePrepare[r] => ToyRM!rmState[r] # "working"
    /\ \forall r \in RMs: (ToyB!oncePrepare[r] /\ ToyRM!rmState[r] = "abort") => ToyB!onceAbort[r]

varsToyRMToyB ==
    <<ToyRM!rmState, ToyB!oncePrepare, ToyB!onceCommit, ToyB!onceAbort>>

\* Init for ToyRM||ToyB ==
InitToyRMToyB ==
    \* ToyRM
    /\ ToyRM!rmState = [rm \in rmState |-> "working"]
    \* ToyB
    /\ ToyB!oncePrepare = [rm \in RMs |-> FALSE]
    /\ ToyB!onceCommit  = [rm \in RMs |-> FALSE]
    /\ ToyB!onceAbort   = [rm \in RMs |-> FALSE]

NextToyRMToyB ==
    \exists rm \in RMs:
        \/ ToyB!Prepare(rm) /\ ToyRM!Prepare(rm) 
        \/ ToyB!Commit(rm) /\ ToyRM!Commit(rm)
        \/ ToyB!Abort(rm) /\ ToyRM!Abort(rm)
        \/ ToyB!SilentAbort(rm) /\ ToyRM!SilentAbort(rm)

\* Testing that candidate inductive invariant is indeed, inductive and invariant. Also checking safety.
THEOREM IrmInitialization == 
    InitToyRMToyB /\ ToyR => Irm
    <1> SUFFICES ASSUME InitToyRMToyB /\ ToyR
                 PROVE Irm
                 OBVIOUS
    <1>. QED
    
THEOREM IrmInduction ==
    Irm /\ NextToyRMToyB /\ ToyR /\ ToyR' => Irm'
    
THEOREM IrmSafety == 
    Irm => Consistent

=============================================================================
\* Modification History
\* Last modified Thu Jun 05 19:07:55 EDT 2025 by johnnguyen
\* Created Thu Jun 05 18:43:08 EDT 2025 by johnnguyen
