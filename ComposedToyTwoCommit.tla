------------------------ MODULE ComposedToyTwoCommit ------------------------
\* Very barbaric, but I'm getting import errors by doing it more elegantly.
\* Just going to pretend it's all in one module

\* Ok I fixed the original problem, I was using \exists and \forall instead of \E and \A 

\* SharedVariables
CONSTANT RMs

\* ToyB variables                            \* ToyRM variable
VARIABLES oncePrepare, onceCommit, onceAbort, rmState

vars ==
    <<rmState, \* ToyRM 
    oncePrepare, onceCommit, onceAbort>> \*ToyB

\* Shared formulae
Init ==
    \* ToyB 
    /\ oncePrepare = [rm \in RMs |-> FALSE]
    /\ onceCommit  = [rm \in RMs |-> FALSE]
    /\ onceAbort    = [rm \in RMs |-> FALSE]
    \* ToyRM
    /\ rmState = [rm \in RMs |-> "working"]
    
Prepare(rm) ==
    \* ToyB
    /\ oncePrepare[rm] = TRUE
    /\ UNCHANGED(onceCommit)
    /\ UNCHANGED(onceAbort)
    \* ToyRM
    /\ rmState[rm] = "working"
    /\ rmState' = [rmState EXCEPT ![rm] = "prepared"]
    
Commit(rm) ==
    \* ToyB
    /\ onceCommit[rm] = TRUE
    /\ UNCHANGED(oncePrepare)
    /\ UNCHANGED(onceAbort)
    \* ToyRM
    /\ rmState' = [rmState EXCEPT ![rm] = "commit"]
    
Abort(rm) ==
    \* ToyB
    /\ onceAbort[rm] = TRUE
    /\ UNCHANGED(oncePrepare)
    /\ UNCHANGED(onceCommit)
    \* ToyRM
    /\ rmState' = [rmState EXCEPT ![rm] = "abort"]
    
\* Just ToyRM
SilentAbort(rm) ==
    /\ rmState[rm] = "working"
    /\ rmState' = [rmState EXCEPT ![rm] = "abort"]  
    
Next ==
    \E rm \in RMs:
        \/ Prepare(rm)
        \/ Commit(rm)
        \/ Abort(rm)
        \/ SilentAbort(rm)

Consistent == \A r1, r2 \in RMs: ~(rmState[r1] = "abort" /\ rmState[r2] = "commit")        
        
ToyR == 
    /\ (\E r \in RMs: onceCommit[r]) => (\A r \in RMs: oncePrepare[r])
    /\ (\E r \in RMs: onceAbort[r])  => (\A r \in RMs: ~onceCommit[r])

Irm == 
    /\ Consistent
    /\ \A r \in RMs: onceCommit[r] <=> rmState[r] = "commit"
    /\ \A r \in RMs: oncePrepare[r] => rmState[r] # "working"
    /\ \A r \in RMs: (oncePrepare[r] /\ rmState[r] = "abort") => onceAbort[r]

\* ToyR is ok to assume, because the other side of the rule application guarantees ToyR
THEOREM IrmInitialization ==
    Init /\ ToyR => Irm
    <1> SUFFICES ASSUME Init /\ ToyR
                 PROVE Irm
                 OBVIOUS 
                 
    <1> SUFFICES ASSUME NEW rm \in RMs, NEW rm2 \in RMs
                 PROVE /\ ~(rmState[rm] = "abort" /\ rmState[rm2] = "commit")
                       /\ onceCommit[rm] <=> rmState[rm] = "commit"
                       /\ oncePrepare[rm] => rmState[rm] # "working"
                       /\ (oncePrepare[rm] /\ rmState[rm] = "abort") => onceAbort[rm]
                 BY DEF Irm, Consistent    
    <1>a ~(rmState[rm] = "abort" /\ rmState[rm2] = "commit") BY DEF Init
    <1>b onceCommit[rm] <=> rmState[rm] = "commit" BY DEF Init
    <1>c oncePrepare[rm] => rmState[rm] # "working" BY DEF Init
    <1>d (oncePrepare[rm] /\ rmState[rm] = "abort") => onceAbort[rm] BY DEF Init
    <1>. QED BY <1>a, <1>b, <1>c, <1>d

THEOREM IrmInduction ==
    Irm /\ Next /\ ToyR /\ ToyR' => Irm'
    <1> SUFFICES ASSUME Irm, ToyR, ToyR', NEW rm \in RMs,
                        Prepare(rm) \/ Commit(rm) \/ Abort(rm) \/ SilentAbort(rm)
                 PROVE Irm'
                 BY DEF Next
                 
    <1> SUFFICES ASSUME NEW rm2 \in RMs, NEW rm3 \in RMs
                 PROVE /\ ~(rmState'[rm2] = "abort" /\ rmState'[rm3] = "commit")
                       /\ onceCommit'[rm2] <=> rmState'[rm2] = "commit"
                       /\ oncePrepare'[rm2] => rmState'[rm2] # "working"
                       /\ (oncePrepare'[rm2] /\ rmState'[rm2] = "abort") => onceAbort'[rm2]
                 BY DEF Irm, Consistent 
                    
    <1>a ~(rmState'[rm2] = "abort" /\ rmState'[rm3] = "commit")
        <2>a CASE Prepare(rm)
        <2>b CASE Commit(rm)
        <2>c CASE Abort(rm)
        <2>d CASE SilentAbort(rm)
        
        <2>. QED BY <2>a, <2>b, <2>c, <2>d
    
    <1>b onceCommit'[rm2] <=> rmState'[rm2] = "commit"
        <2>a CASE Prepare(rm)
        <2>b CASE Commit(rm)
        <2>c CASE Abort(rm)
        <2>d CASE SilentAbort(rm)
        
        <2>. QED BY <2>a, <2>b, <2>c, <2>d
    
    <1>c oncePrepare'[rm2] => rmState'[rm2] # "working"
        <2>a CASE Prepare(rm)
        <2>b CASE Commit(rm)
        <2>c CASE Abort(rm)
        <2>d CASE SilentAbort(rm)
        
        <2>. QED BY <2>a, <2>b, <2>c, <2>d
    
    <1>d (oncePrepare'[rm2] /\ rmState'[rm2] = "abort") => onceAbort'[rm2]
        <2>a CASE Prepare(rm)
        <2>b CASE Commit(rm)
        <2>c CASE Abort(rm)
        <2>d CASE SilentAbort(rm)
        
        <2>. QED BY <2>a, <2>b, <2>c, <2>d
    
    <1>. QED BY <1>a, <1>b, <1>c, <1>d
    
THEOREM IrmSafety ==
    Irm => Consistent BY DEF Irm

=============================================================================
\* Modification History
\* Last modified Fri Jun 06 10:49:11 EDT 2025 by johnnguyen
\* Created Thu Jun 05 20:01:22 EDT 2025 by johnnguyen
