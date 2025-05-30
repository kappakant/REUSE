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

I == \A p, q \in {0, 1}: (p#q /\ processState[p] = "critical") => (flag[q] = FALSE \/ turn = p \/ processState[q] = "sentRequest") \* sentRequest is an intermezzo before switching turns
                          

Inv == /\ TypeOK
       /\ I
       /\ MutualExclusion

Inv2 == \A p, q: processState[p] /= "critical"
Inv3 == ~ \E p: processState[p] = "critical"


THEOREM InitProperty == Init => Inv
    BY DEF Init, Inv, ProcessRequestFlag, ProcessBeginWaiting, ProcessEnterCritical, ProcessExitCritical, TypeOK, MutualExclusion

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

            <3>2. I'
                <4>1 I BY DEF Inv
                <4>2 \A m, n \in {0, 1}: (m#n /\ processState[m] = "critical") => (flag[n] = FALSE \/ turn = m \/ processState[n] = "sentRequest") BY DEF Inv, I
                
                <4>3 (0#1 /\ processState[0] = "critical") => (flag[1] = FALSE \/ turn = 0 \/ processState[1] = "sentRequest") BY <4>2
                <4>4 turn' = turn BY <2>a DEF ProcessRequestFlag
                <4>5 flag' = [flag EXCEPT ![0] = TRUE] BY <2>a DEF ProcessRequestFlag
                <4>6 flag'[1] = flag[1] BY <4>5, <4>3
                <4>7 processState' = [processState EXCEPT ![0] = "sentRequest"] BY <2>a DEF ProcessRequestFlag
                <4>8 processState'[1] = processState[1] BY <4>7, <4>3
                <4>9 (0#1 /\ processState[0] = "critical") => (flag[1] = FALSE \/ turn = 0 \/ processState[1] = "sentRequest")' BY <4>3, <4>4, <4>6, <4>8
                <4>10 (0#1 /\ processState[0] = "critical")' => (0#1 /\ processState[0] = "critical")
                <4> SUFFICES ASSUME (0#1 /\ processState[0] = "critical")'
                             PROVE (0#1 /\ processState[0] = "critical")
                             
                <4>11 (0#1 /\ processState[0] = "critical")' => (flag[1] = FALSE \/ turn = 0 \/ processState[1] = "sentRequest")' BY <4>9, <4>10
        
                \* Not necessarily true
                <4>20 ((~\E m, n \in {0, 1}: (m#n /\ processState[m] = "critical"))')
                <4>. QED BY <4>20 DEF I
               
                \* material implication strategy
                (***********************************************************
                <4>1. TAKE p, q \in {0, 1}
                <4>2. ~(p#q /\ processState'[p] = "critical") \/ (flag'[q] = FALSE \/ turn' = p \/ processState'[q] = "sentRequest") => (flag'[q] = FALSE \/ turn' = p \/ processState'[q] = "sentRequest")
                <4>3. SUFFICES ASSUME ~(p#q /\ processState'[p] = "critical") \/ (flag'[q] = FALSE \/ turn' = p \/ processState'[q] = "sentRequest")
                               PROVE (flag'[q] = FALSE \/ turn' = p \/ processState'[q] = "sentRequest") BY <4>2
                <4>. QED
                 ***********************************************************)
                 
            <3>3. MutualExclusion'
                <4>1 MutualExclusion BY DEF Inv
                <4>2 ~processState[0] = "critical" \/ ~processState[1] = "critical" BY <4>1 DEF MutualExclusion
                <4>3 I BY DEF Inv
                
                \* W.L.O.G
                <4>a CASE processState[0] # "critical" /\ processState[1] = "critical"
                    <5>1 TRUE
                    <5>. QED
   
\*                (***********************************************************
\*                <4> SUFFICES ASSUME ~MutualExclusion'
\*                             PROVE FALSE
\*                <4>3 processState'[0] = "critical" /\ processState'[1] = "critical" BY DEF MutualExclusion
\*                
\*                \* Intuitively obvious, but I'm having the EXCEPT problem
\*                <4>4 (processState'[0] = "critical" <=> ProcessEnterCritical(0)) /\ (processState'[1] = "critical" <=> ProcessEnterCritical(1))
\*                    <5> ASSUME Next
\*                        PROVE (processState'[0] = "critical" <=> ProcessEnterCritical(0)) /\ (processState'[1] = "critical" <=> ProcessEnterCritical(1))
\*                    <5>a CASE Process0
\*                        <6>a CASE ProcessRequestFlag(0)
\*                           OBVIOUS
\*                        <6>b CASE ProcessBeginWaiting(0)
\*                           OBVIOUS
\*                        <6>c CASE ProcessEnterCritical(0)
\*                           OBVIOUS
\*                        <6>d CASE ProcessExitCritical(0)
\*                           OBVIOUS
\*                        <6>. QED BY <6>a, <6>b, <6>c, <6>d
\*                    <5>b CASE Process1
\*                        <6>a CASE ProcessRequestFlag(1)
\*                           OBVIOUS
\*                        <6>b CASE ProcessBeginWaiting(1)
\*                           OBVIOUS
\*                        <6>c CASE ProcessEnterCritical(1)
\*                           OBVIOUS
\*                        <6>d CASE ProcessExitCritical(1)
\*                           OBVIOUS
\*                        <6>. QED BY <6>a, <6>b, <6>c, <6>d
\*                    <5>. QED BY <5>a, <5>b
\*
\*                <4>5 ProcessEnterCritical(0) BY <4>4, <4>3
\*                <4>6 flag[1] = FALSE \/ turn = 0 \/ processState[1] = "sentRequest" BY <4>5 DEF ProcessEnterCritical
\*                
\*                <4>a CASE flag[1] = FALSE
\*                
\*                <4>b CASE turn = 0
\*                
\*                <4>c CASE processState[1] = "sentRequest"
\*                    <5>1 processState[1] # "waiting" BY <4>c
\*                    <5>2 ~ProcessEnterCritical(1) BY <4>4, <5>1 DEF ProcessEnterCritical
\*                    <5>3 processState'[1] # "critical" BY <4>4, <5>2
\*                    <5>4 processState'[1] # "critical" /\ processState'[1] = "critical" BY <4>3, <5>3
\*                    <5>. QED BY <5>4
\*                 ***********************************************************)
                <4>10 processState'[0] # "critical" \/ processState'[1] # "critical"
                
                
                <4>11 processState' = [processState EXCEPT ![0] = "sentRequest"] BY <2>a DEF ProcessRequestFlag
                <4>12 processState'[0] # "critical" \* BY <4>11
                
                <4>. QED BY <4>12 DEF MutualExclusion
            <3>. QED BY <3>1, <3>2, <3>3 DEF Inv
        <2>b CASE ProcessBeginWaiting(0)
            <3>1 TypeOK'
                <4>1. TypeOK BY DEF Inv
                <4>2. turn' \in {0, 1} BY <2>b DEF Inv, TypeOK, ProcessBeginWaiting
                <4>3. \A p \in {0, 1}: flag'[p] \in {TRUE, FALSE} 
                    <5>1. \A p \in {0, 1}: flag[p] \in {TRUE, FALSE} BY <2>b DEF TypeOK, Inv
                    <5>2. flag' = flag BY <2>b DEF ProcessBeginWaiting
                    <5>3. flag' \in [{0,1} -> {TRUE, FALSE}] BY <5>2 DEF Inv, TypeOK
                    <5>. QED BY <5>1, <5>2, <5>3 DEF Inv
                <4>4. processState' \in [{0,1} -> {"idle", "sentRequest", "waiting", "critical"}]
                    <5>1. processState \in [{0,1} -> {"idle", "sentRequest", "waiting", "critical"}] BY <2>b DEF Inv, TypeOK, ProcessBeginWaiting
                    <5>2. processState' = [processState EXCEPT ![0] = "waiting"] BY <2>b DEF ProcessBeginWaiting
                    <5>3. processState' \in [{0,1} -> {"idle", "sentRequest", "waiting", "critical"}] BY <5>2 DEF Inv, TypeOK
                    <5>. QED BY <5>1, <5>2, <5>3 DEF Inv
                <4>. QED BY <2>b, <4>1, <4>2, <4>3, <4>4 DEF Inv, TypeOK, ProcessBeginWaiting
                
            <3>2 I'
                <4> PICK p: p \in {0, 1}
                <4> PICK q: q \in {0, 1}
                <4> SUFFICES ASSUME (p#q /\ processState[p] = "critical")'
                             PROVE (flag[q] = FALSE \/ turn = p \/ processState[q] = "sentRequest")'
                             OBVIOUS
                <4>. QED
            
            \* This really should be working
            <3>3 MutualExclusion'
                <4>1 processState' = [processState EXCEPT ![0] = "waiting"] BY <2>b DEF ProcessBeginWaiting
                <4>2 processState'[0] # "critical" \* BY <4>1 DEF ProcessBeginWaiting
                <4>. QED BY <4>1 DEF MutualExclusion
            
            <3>. QED BY <3>1, <3>2, <3>3 DEF Inv
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
\* Last modified Fri May 30 02:43:04 EDT 2025 by johnnguyen
\* Created Wed May 28 01:17:56 EDT 2025 by johnnguyen
