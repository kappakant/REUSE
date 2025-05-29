------------------------------ MODULE Peterson ------------------------------
EXTENDS Integers, TLAPS

VARIABLES 
    turn, (*****************************************************************)
          (* This is one of the three items that mutate in Peterson's      *)
          (* algorithm.  It is what keeps track of which process's turn it *)
          (* is to access the shared resource                              *)
          (*****************************************************************)
    processState, (*********************************************************)
                  (* This is a function mapping each process (represented  *)
                  (* by an integer 0 or 1) to its current state (a         *)
                  (* string).                                              *)
                  (*********************************************************)
    flag (******************************************************************)
         (* This contains the remaining two of the three items that mutate *)
         (* in Peterson' algorithm.  It is a function mapping each process *)
         (* (represented by an integer 0 or 1) to a boolean flag           *)
         (* indicating whether the process would like to access the shared *)
         (* resource.                                                      *)
         (******************************************************************)

vars == <<turn, processState, flag>> (**************************************)
                                     (* This is simply a convenient        *)
                                     (* grouping of variables to use later *)
                                     (* on when defining temporal          *)
                                     (* properties to save on tedious      *)
                                     (* typing.                            *)
                                     (**************************************)

(***************************************************************************)
(* )                                                                       *)
(* TypeOK ==                                                               *)
(*     /\ \A p \in {0, 1} : flag[p] \in {TRUE, FALSE}                      *)
(*     /\ turn \in {0, 1}                                                  *)
(*     /\ \A p \in {0, 1} : processState[p] \in {"idle", "sentRequest", "waiting", "critical"} *)
(* (                                                                       *)
(***************************************************************************)
    
\* use typeok2 in second proof
\* Hell, Use TypeOK2 as TypeOK!
TypeOK ==  
    /\ turn \in {0, 1}
    /\ flag \in [{0,1} -> {TRUE,FALSE}]
    /\ processState \in [{0,1} -> {"idle", "sentRequest", "waiting", "critical"}]

(***************************************************************************)
(* This is one possible initial state of Peterson's algorithm.  It is the  *)
(* most "natural" one, that is the one where both processes are idle and   *)
(* have not yet decided to access the resource.                            *)
(***************************************************************************)
Init ==
    /\ flag = [i \in {0, 1} |-> FALSE]
    /\ turn \in {0, 1}
    /\ processState = [i \in {0, 1} |-> "idle"]
    
(***************************************************************************)
(* This predicate describes how a process can send a request to access a   *)
(* resource, which essentially amounts to setting its request flag to      *)
(* true.                                                                   *)
(***************************************************************************)    
ProcessRequestFlag(p) ==
    /\ processState[p] = "idle"
    /\ flag' = [flag EXCEPT ![p] = TRUE]
    /\ processState' = [processState EXCEPT ![p] = "sentRequest"]
    /\ UNCHANGED <<turn>>

ProcessBeginWaiting(p) ==
    /\ processState[p] = "sentRequest"
    /\ turn' = 1 - p
    /\ processState' = [processState EXCEPT ![p] = "waiting"]
    /\ UNCHANGED <<flag>>
    
ProcessEnterCritical(p) ==
    /\ processState[p] = "waiting"
    /\ (flag[(1 - p)] = FALSE \/ turn = p)
    /\ processState' = [processState EXCEPT ![p] = "critical"]
    /\ UNCHANGED <<flag, turn>>

ProcessExitCritical(p) ==
    /\ processState[p] = "critical"
    /\ processState' = [processState EXCEPT ![p] = "idle"]
    /\ flag' = [flag EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<turn>>

(***************************************************************************
\(*
Next ==
    \E p \in {0, 1} :
        \/ ProcessRequestFlag(p)
        \/ ProcessBeginWaiting(p)
        \/ ProcessEnterCritical(p)
        \/ ProcessExitCritical(p)
\*)
 ***************************************************************************)

Process0 == \/ ProcessRequestFlag(0)
            \/ ProcessBeginWaiting(0)
            \/ ProcessEnterCritical(0)
            \/ ProcessExitCritical(0)
            
Process1 == \/ ProcessRequestFlag(1)
            \/ ProcessBeginWaiting(1)
            \/ ProcessEnterCritical(1)
            \/ ProcessExitCritical(1)
Next == Process0 \/ Process1
\* Surely this is equivalent. Idk why internet says TLAPS proof for this, asserting IFF should be enough?
\* Not recommended - Ian
    
Spec == Init /\ [][Next]_vars 

SpecWithFairness == Spec /\ WF_vars(Next) /\ \A p \in {0, 1} : WF_vars(ProcessRequestFlag(p))

MutualExclusion == ~(processState[0] = "critical" /\ processState[1] = "critical")

THEOREM Spec => []MutualExclusion

(***************************************************************************)
(* This is a basic liveness requirement that corresponds to what is called *)
(* "Progress" in the Wikipedia article.  Both processes should eventually  *)
(* be able to enter their critical sections.                               *)
(***************************************************************************)
WillEventuallyEnterCritical == <>(processState[0] = "critical") /\ <>(processState[1] = "critical")

THEOREM SpecWithFairness => WillEventuallyEnterCritical

(***************************************************************************)
(* THIS INVARIANT DOES NOT HOLD AND SHOULD NOT HOLD! It's merely           *)
(* instructive of something a reader may intuitively believe about this    *)
(* algorithm that turns out to be false.                                   *)
(*                                                                         *)
(* See the note in ProcessEnterCritical.                                   *)
(***************************************************************************)
CanOnlyBeCriticalIfTurn == \A p \in {0, 1} : processState[p] = "critical" => turn = p

(***************************************************************************)
(* Finally we note simply that our variables should always stay within the *)
(* bounds we enumerated earlier.                                           *)
(***************************************************************************)
THEOREM TypeCheck == Spec => []TypeOK

Inv == /\ TypeOK
       /\ \A p, q \in {0, 1}: \/ processState[p] = "critical" => (flag[q] = FALSE \/ turn = p \/ processState[q] = "sentRequest") \* sentRequest is an intermezzo before switching turns
                              \/ p = q \* removes scenarios which don't properly model the system, perhaps not idiomatic
       /\ MutualExclusion

Inv2 == \A p, q: processState[p] /= "critical"
Inv3 == ~ \E p: processState[p] = "critical"


THEOREM InitProperty == Init => Inv
    BY DEF Init, Inv, ProcessRequestFlag, ProcessBeginWaiting, ProcessEnterCritical, ProcessExitCritical, TypeOK, MutualExclusion

THEOREM SafetyProperty == Inv => MutualExclusion
    BY DEF Inv, MutualExclusion

(***************************************************************************)
(* THEOREM InductProperty == Inv /\ Next => Inv'                           *)
(* <1> SUFFICES ASSUME Inv, Next                                           *)
(*              PROVE Inv'                                                 *)
(* <1> USE DEF Inv, Next                                                   *)
(***************************************************************************)

\* Figure out how to prove internal propositions
\* nvm I just broke it. Next or [Next]_vars? Are stutter steps really that big of a deal?

THEOREM InductProperty == Inv /\ Next => Inv'
    <1> SUFFICES ASSUME Inv, Next
                 PROVE Inv'
                 OBVIOUS
    \*<1> USE DEF Inv, Next  
    <1>1 Process0 \/ Process1 \* Stutter stepping would change anything? 
         BY DEF Next
    <1>a CASE Process0
        <2>1 ProcessRequestFlag(0) \/ ProcessBeginWaiting(0) \/ ProcessEnterCritical(0) \/ ProcessExitCritical(0)
            BY <1>a DEF Process0
        <2>a CASE ProcessRequestFlag(0) \* BY DEF ProcessRequestFlag, MutualExclusion, TypeOK
            <3>1. TypeOK'
                <4>1. TypeOK BY DEF Inv
                <4>2. turn' \in {0, 1} BY <2>a DEF Inv, TypeOK, ProcessRequestFlag
                <4>3. \A p \in {0, 1}: flag'[p] \in {TRUE, FALSE} 
                    <5>1. \A p \in {0, 1}: flag[p] \in {TRUE, FALSE} BY <2>a DEF TypeOK, Inv
                    <5>2. flag' = [flag EXCEPT ![0] = TRUE] BY <2>a DEF ProcessRequestFlag
                    <5>3. flag' \in [{0,1} -> {TRUE, FALSE}] BY <5>2 DEF Inv, TypeOK
                    <5>. QED BY <5>1, <5>2, <5>3 DEF Inv
                <4>4. processState' \in [{0,1} -> {"idle", "sentRequest", "waiting", "critical"}]
                    <5>1. processState \in [{0,1} -> {"idle", "sentRequest", "waiting", "critical"}] BY <2>a DEF Inv, TypeOK, ProcessRequestFlag
                    <5>2. processState' = [processState EXCEPT ![0] = "sentRequest"] BY <2>a DEF ProcessRequestFlag
                    <5>3. processState' \in [{0,1} -> {"idle", "sentRequest", "waiting", "critical"}] BY <5>2 DEF Inv, TypeOK
                    <5>. QED BY <5>1, <5>2, <5>3 DEF Inv
                <4>. QED BY <2>a, <4>1, <4>2, <4>3, <4>4 DEF Inv, TypeOK, ProcessRequestFlag

            <3>2. \A p, q \in {0, 1}: (p#q /\ processState'[p] = "critical") => (flag'[q] = FALSE \/ turn' = p \/ processState'[q] = "sentRequest")
                <4>1. TAKE p, q \in {0, 1}
                <4>2. SUFFICES ASSUME p#q, processState'[p] = "critical"
                               PROVE flag'[q] = FALSE \/ turn' = p \/ processState'[q] = "sentRequest"
                               OBVIOUS
                <4>a CASE p#q
                <4>b CASE processState'[p] = "critical"
                <4>. QED BY <4>a, <4>b
                
            <3>3. MutualExclusion'
            <3>. QED BY <3>1, <3>2, <3>3 DEF Inv
        <2>b CASE ProcessBeginWaiting(0)
        <2>c CASE ProcessEnterCritical(0)
        <2>d CASE ProcessExitCritical(0)
        <2> QED BY <2>1, <2>a, <2>b, <2>c, <2>d DEF ProcessRequestFlag, ProcessBeginWaiting, ProcessEnterCritical, ProcessExitCritical, TypeOK, MutualExclusion
    <1>b CASE Process1
        <2>1 ProcessRequestFlag(1) \/ ProcessBeginWaiting(1) \/ ProcessEnterCritical(1) \/ ProcessExitCritical(1)
            BY <1>b DEF Process1
        <2>a CASE ProcessRequestFlag(1)
            <3>1. TypeOK'
                <4>1. TypeOK BY DEF Inv
                <4>2. turn' \in {0, 1} BY <2>a DEF Inv, TypeOK, ProcessRequestFlag
                <4>3. \A p \in {0, 1}: flag'[p] \in {TRUE, FALSE} 
                    <5>1. \A p \in {0, 1}: flag[p] \in {TRUE, FALSE} BY <2>a DEF TypeOK, Inv
                    <5>2. flag' = [flag EXCEPT ![1] = TRUE] BY <2>a DEF ProcessRequestFlag
                    <5>3. flag' \in [{0,1} -> {TRUE, FALSE}] BY <5>2 DEF Inv, TypeOK
                    <5>. QED BY <5>1, <5>2, <5>3 DEF Inv
                <4>4. processState' \in [{0,1} -> {"idle", "sentRequest", "waiting", "critical"}]
                    <5>1. processState \in [{0,1} -> {"idle", "sentRequest", "waiting", "critical"}] BY <2>a DEF Inv, TypeOK, ProcessRequestFlag
                    <5>2. processState' = [processState EXCEPT ![1] = "sentRequest"] BY <2>a DEF ProcessRequestFlag
                    <5>3. processState' \in [{0,1} -> {"idle", "sentRequest", "waiting", "critical"}] BY <5>2 DEF Inv, TypeOK
                    <5>. QED BY <5>1, <5>2, <5>3 DEF Inv
                <4>. QED BY <2>a, <4>1, <4>2, <4>3, <4>4 DEF Inv, TypeOK, ProcessRequestFlag
             <3>. QED
        <2>b CASE ProcessBeginWaiting(1)
        <2>c CASE ProcessEnterCritical(1)
        <2>d CASE ProcessExitCritical(1)
        <2> QED BY <2>1, <2>a, <2>b, <2>c, <2>d
    <1> QED BY <1>1, <1>a, <1>b

THEOREM InvariantProperty == Spec => []Inv
    <1>1 Init => Inv BY InitProperty
    <1>2 Inv /\ Next => Inv' BY InductProperty
    <1> QED BY <1>1, <1>2, PTL, TypeCheck DEF Init, Inv, Next, MutualExclusion

THEOREM Correctness == Spec => []MutualExclusion
    <1>1 Inv /\ UNCHANGED<<flag, turn, processState>> => Inv' 
        BY DEF Inv, TypeOK, MutualExclusion
    
    \* Define this in another theorem
    <1>2 Spec => []Inv \* Split into cases? Feels like the problem is the proof is too large.
                       \* How to simply non-disjunctions? Convert implications into disjunctions?
        BY InitProperty, InductProperty, PTL, <1>1 DEF Spec, Init, Inv, Next, MutualExclusion
        
    <1>3 Inv => MutualExclusion
        BY SafetyProperty DEF Inv, MutualExclusion
    <1> QED BY <1>1, <1>2, <1>3, PTL \* Doesn't need <1>1, which is interesting.
==================================================
\* Modification History
\* Last modified Thu May 29 14:37:30 EDT 2025 by johnnguyen
\* Created Wed May 28 01:17:56 EDT 2025 by johnnguyen
