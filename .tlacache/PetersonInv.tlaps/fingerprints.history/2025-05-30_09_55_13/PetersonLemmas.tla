--------------------------- MODULE PetersonLemmas ---------------------------
EXTENDS Peterson

THEOREM PRFInduction0 == Inv /\ Next /\ ProcessRequestFlag(0) => Inv'
    <1> SUFFICES ASSUME Inv, Next, ProcessRequestFlag(0)
                 PROVE Inv'
                 OBVIOUS
    <1>. QED
    
THEOREM PBWInduction0 == Inv /\ Next /\ ProcessBeginWaiting(0) => Inv'
    <1> SUFFICES ASSUME Inv, Next, ProcessBeginWaiting(0)
                 PROVE Inv'
                 OBVIOUS
    <1>. QED
    
THEOREM PEnCInduction0 == Inv /\ Next /\ ProcessEnterCritical(0) => Inv'
    <1> SUFFICES ASSUME Inv, Next, ProcessEnterCritical(0)
                 PROVE Inv'
                 OBVIOUS
    <1>. QED
    
THEOREM PExCInduction0 == Inv /\ Next /\ ProcessExitCritical(0) => Inv'
    <1> SUFFICES ASSUME Inv, Next, ProcessExitCritical(0)
                 PROVE Inv'
                 OBVIOUS
    <1>. QED
    
THEOREM PRFInduction1 == Inv /\ Next /\ ProcessRequestFlag(1) => Inv'
    <1> SUFFICES ASSUME Inv, Next, ProcessRequestFlag(1)
                 PROVE Inv'
                 OBVIOUS
    <1>. QED
    
THEOREM PBWInduction1 == Inv /\ Next /\ ProcessBeginWaiting(1) => Inv'
    <1> SUFFICES ASSUME Inv, Next, ProcessBeginWaiting(1)
                 PROVE Inv'
                 OBVIOUS
    <1>. QED
    
THEOREM PEnCInduction1 == Inv /\ Next /\ ProcessEnterCritical(1) => Inv'
    <1> SUFFICES ASSUME Inv, Next, ProcessEnterCritical(1)
                 PROVE Inv'
                 OBVIOUS
    <1>. QED
    
THEOREM PExCInduction1 == Inv /\ Next /\ ProcessExitCritical(1) => Inv'
    <1> SUFFICES ASSUME Inv, Next, ProcessExitCritical(1)
                 PROVE Inv'
                 OBVIOUS
    <1>. QED

=============================================================================
\* Modification History
\* Last modified Fri May 30 09:53:29 EDT 2025 by johnnguyen
\* Created Fri May 30 09:25:52 EDT 2025 by johnnguyen
