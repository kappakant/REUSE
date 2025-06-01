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


\* Removed MutualExclusion because it's more difficult in InductProperty.
\* JK it's much harder this way
(***************************************************************************
THEOREM SafetyProperty == Inv => MutualExclusion
    <1> SUFFICES ASSUME Inv
                 PROVE MutualExclusion
        OBVIOUS
    <1>1. I BY DEF Inv
    <1> SUFFICES ASSUME ~MutualExclusion
                  PROVE FALSE
    <1>2 processState[1] = "critical" BY DEF MutualExclusion
                  
    <1>3 processState[0] = "critical" BY DEF MutualExclusion
    <1>4 processState[0] = "critical" => (flag[1] = FALSE \/ turn = 0 \/ processState[1] = "sentRequest") BY <1>1 DEF I
    <1>5 (flag[1] = FALSE \/ turn = 0 \/ processState[1] = "sentRequest") BY <1>3, <1>4
    
    <1>a CASE flag[1] = FALSE
    
    <1>b CASE turn = 0
    
    <1>c CASE processState[1] = "sentRequest"
        <2>1 processState[1] = "sentRequest" /\ processState[1] = "critical" BY <1>c, <1>2
        <2>. QED BY <2>1
        
    <1>. QED BY <1>a, <1>b, <1>c, <1>5
 ***************************************************************************)


(***************************************************************************)
(* THEOREM InductProperty == Inv /\ Next => Inv'                           *)
(* <1> SUFFICES ASSUME Inv, Next                                           *)
(*              PROVE Inv'                                                 *)
(* <1> USE DEF Inv, Next                                                   *)
(***************************************************************************)

\* Figure out how to prove internal propositions
\* nvm I just broke it. Next or [Next]_vars? Are stutter steps really that big of a deal?
\* Importing lemmas instead
critReqs(p, q) == 
    (p#q /\ processState[p] = "critical") => /\ flag[q] = FALSE \/ turn = p \/ processState[q] = "sentRequest" 
                                             /\ flag[p] = TRUE

requestReqs(p, q) == 
    (p#q /\ processState[p] = "sentRequest") => flag[p] = TRUE

waitReqs(p, q) ==
    (p#q /\ processState[p] = "waiting") => flag[p] = TRUE

I == \A p, q \in {0, 1}: 
    /\ critReqs(p, q)                                                    
    \*/\ requestReqs(p, q)
    /\ waitReqs(p, q)
    

Inv == /\ TypeOK
       /\ I
       /\ MutualExclusion
       
IndSpec == Inv /\ [][Next]_vars

MutExSpec == MutualExclusion /\ [][Next]_vars

==================================================
\* Modification History
\* Last modified Sun Jun 01 17:43:51 EDT 2025 by johnnguyen
\* Created Wed May 28 01:17:56 EDT 2025 by johnnguyen
