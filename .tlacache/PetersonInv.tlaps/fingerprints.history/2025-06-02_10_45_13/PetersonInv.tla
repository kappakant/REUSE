---------------------------- MODULE PetersonInv ----------------------------
EXTENDS Peterson, PetersonLemmas

THEOREM InitProperty == Init => Inv
    BY DEF Init, Inv, ProcessRequestFlag, ProcessBeginWaiting, ProcessEnterCritical, ProcessExitCritical, TypeOK, MutualExclusion

 THEOREM SafetyProperty == Inv => MutualExclusion
    BY DEF Inv, MutualExclusion

THEOREM InductProperty == Inv /\ Next => Inv'
<1> SUFFICES ASSUME Inv, Next
             PROVE Inv'
             OBVIOUS
             
<1>1 Process0 \/ Process1 BY DEF Next
<1>a CASE Process0
    <2>1 ProcessRequestFlag(0) \/ ProcessBeginWaiting(0) \/ ProcessEnterCritical(0) \/ ProcessExitCritical(0)
            BY <1>a DEF Process0
            
    <2>a CASE ProcessRequestFlag(0) 
        BY <2>a, PRFInduction0 
    
    <2>b CASE ProcessBeginWaiting(0)
        BY <2>b, PBWInduction0
    
    <2>c CASE ProcessEnterCritical(0)
        BY <2>c, PEnCInduction0
    
    <2>d CASE ProcessExitCritical(0)
        BY <2>d, PExCInduction0
    
    <2>. QED BY <1>a, <2>1, <2>a, <2>b, <2>c, <2>d DEF Inv

<1>b CASE Process1
    \* Unofficially, Process0 implies Process1
    <2>1 ProcessRequestFlag(1) \/ ProcessBeginWaiting(1) \/ ProcessEnterCritical(1) \/ ProcessExitCritical(1)
            BY <1>b DEF Process1
            
    <2>a CASE ProcessRequestFlag(1) 
        BY <2>a, PRFInduction1
    
    <2>b CASE ProcessBeginWaiting(1)
        BY <2>b, PBWInduction1
    
    <2>c CASE ProcessEnterCritical(1)
        BY <2>c, PEnCInduction1
    
    <2>d CASE ProcessExitCritical(1)
        BY <2>d, PExCInduction1
    
    <2>. QED BY <1>a, <2>1, <2>a, <2>b, <2>c, <2>d DEF Inv

<1>. QED BY <1>1, <1>a, <1>b

=============================================================================
\* Modification History
\* Last modified Mon Jun 02 10:45:10 EDT 2025 by johnnguyen
\* Created Fri May 30 09:25:17 EDT 2025 by johnnguyen

