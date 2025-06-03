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

\* if abort then not commit /\
\* if commit then not abort

\* actually, if commit then not abort is good enough
\* consider quantifying over something else, like tmPrepared?
\* maybe a combo of checking tmState and tmPrepared is necessary.
(***************************************************************************
\* I == \A r1, r2 \in RMs: 
\*    (r1#r2 /\ rmState[r1] = "commit") => tmPrepared = RMs
 ***************************************************************************)
 \* passes tests, but do I really trust that it's that easy?
I == 
    \A rm \in tmPrepared:
        /\ tmState = "init" => rmState[rm] = "prepared"
        /\ tmState = "abort" => (rmState[rm] = "prepared" \/ rmState[rm] = "abort") /\ tmPrepared = RMs 
        /\ tmState = "commit" => /\ rmState[rm] = "prepared" \/ rmState[rm] = "commit"
                                 
    
CandInv == 
    /\ I
    /\ TypeOK

TestSpec == TypeOK /\ Init /\ [][Next]_vars

TestIndSpec == TypeOK /\ CandInv /\ [][Next]_vars   
 
TestSafety == CandInv => Consistent

TestInd == CandInv /\ Next => CandInv'

TestInit == Init => CandInv

Inv == 
    /\ TypeOK
    /\ I
    
=============================================================================
\* Modification History
\* Last modified Mon Jun 02 22:17:30 EDT 2025 by johnnguyen
\* Created Sat May 31 21:17:41 EDT 2025 by johnnguyen
