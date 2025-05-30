--------------------------- MODULE PetersonLemmas ---------------------------
EXTENDS Peterson

THEOREM PRFInduction == Inv /\ Next /\ ProcessRequestFlag(0) => Inv'
    <1> SUFFICES ASSUME Inv, Next, ProcessRequestFlag(0)
                 PROVE Inv'
                 OBVIOUS
    <1>. QED
    
THEOREM PBWInduction == Inv /\ Next /\ ProcessBeginWaiting(0) => Inv'
    <1> SUFFICES ASSUME Inv, Next, ProcessBeginWaiting(0)
                 PROVE Inv'
                 OBVIOUS
    <1>. QED
    
THEOREM PEnCInduction == Inv /\ Next /\ ProcessEnterCritical(0) => Inv'
    <1> SUFFICES ASSUME Inv, Next, ProcessEnterCritical(0)
                 PROVE Inv'
                 OBVIOUS
    <1>. QED
    
THEOREM PExCInduction == Inv /\ Next /\ ProcessExitCritical(0) => Inv'
    <1> SUFFICES ASSUME Inv, Next, ProcessExitCritical(0)
                 PROVE Inv'
                 OBVIOUS
    <1>. QED

=============================================================================
\* Modification History
\* Last modified Fri May 30 09:51:03 EDT 2025 by johnnguyen
\* Created Fri May 30 09:25:52 EDT 2025 by johnnguyen
