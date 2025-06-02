---------------------------- MODULE ToyTwoCommit ----------------------------
EXTENDS Integers

CONSTANT RMs

VARIABLES rmState, tmState, tmPrepared

vars == <<rmState, tmState, tmPrepared>>

Init == 
    /\ rmState = [rm \in RMs |-> "working"]
    /\ tmState = "init"
    /\ tmPrepared = {}
    
TypeOK ==
    /\ rmState \in [RMs -> {"working", "prepared", "commit", "abort"}]
    /\ tmState \in {"init", "commit", "abort"}
    /\ tmPrepared \in SUBSET RMs \* Weird, but documented quirk of TLC is that the more natural
                                 \* tmPrepared \subseteq RMs leads to an "undefined operator" error.
    
Prepare(rm) ==
    /\ rmState[rm] = "working" 
    /\ tmState = "init"
    /\ rmState' = [rmState EXCEPT ![rm] = "prepared"]
    /\ tmPrepared' = tmPrepared \cup {rm}
    /\ UNCHANGED(tmState)

Commit(rm) ==
    /\ tmState \in {"init", "commit"}
    /\ tmPrepared = RMs
    /\ rmState' = [rmState EXCEPT ![rm] = "commit"]
    /\ tmState' = "commit"
    /\ UNCHANGED(tmPrepared)

Abort(rm) == 
    /\ tmState \in {"init", "abort"}
    /\ rmState' = [rmState EXCEPT ![rm] = "abort"]
    /\ tmState' = "abort"
    /\ UNCHANGED(tmPrepared)

SilentAbort(rm) ==
    /\ rmState[rm] = "working"
    /\ rmState' = [rmState EXCEPT ![rm] = "abort"]
    /\ UNCHANGED(tmPrepared) /\ UNCHANGED(tmState)
    
Next == 
    \E rm \in RMs:
    \/ Prepare(rm)
    \/ Commit(rm)
    \/ Abort(rm)
    \/ SilentAbort(rm)

(***************************************************************************
\/ TMCommit \/ TMAbort
  \/ \E r \in RM : 
       TMRcvPrepared(r) \/ RMPrepare(r) \/ RMChooseToAbort(r)
         \/ RMRcvCommitMsg(r) \/ RMRcvAbortMsg(r)
 ***************************************************************************)

Consistent == \A r1, r2 \in RMs: ~(rmState[r1] = "abort" /\ rmState[r2] = "commit")

I == \A r1, r2 \in RMs: 
    (r1#r2 /\ rmState[r1] = "abort") => tmPrepared # RMs

CandInv == 
    /\ I
    /\ TypeOK

TestIndSpec == TypeOK /\ CandInv /\ [][Next]_vars   
 
TestSafety == CandInv => Consistent

TestInd == CandInv /\ Next => CandInv'

TestInit == Init => CandInv
=============================================================================
\* Modification History
\* Last modified Mon Jun 02 14:44:20 EDT 2025 by johnnguyen
\* Created Sat May 31 21:17:41 EDT 2025 by johnnguyen
