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


TypeOK ==
    /\ \A p \in {0, 1} : flag[p] \in {TRUE, FALSE}
    /\ turn \in {0, 1}
    /\ \A p \in {0, 1} : processState[p] \in {"idle", "sentRequest", "waiting", "critical"}
    
TypeOk2 ==
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
THEOREM Spec => []TypeOK

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
(* <1> USE DEF Inv, Next \                                                 *)
(***************************************************************************)

  
==================================================
\* Modification History
\* Last modified Thu May 29 09:12:06 EDT 2025 by johnnguyen
\* Created Wed May 28 01:17:56 EDT 2025 by johnnguyen
