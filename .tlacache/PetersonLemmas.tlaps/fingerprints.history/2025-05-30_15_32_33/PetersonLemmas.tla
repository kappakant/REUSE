--------------------------- MODULE PetersonLemmas ---------------------------
EXTENDS Peterson

\* Ok, so we're on the right track I think. Surely that nagging case isn't going to be super punishing.
\* Ian seemed to think that 
THEOREM PRFInduction0 == Inv /\ Next /\ ProcessRequestFlag(0) => Inv'
    <1> SUFFICES ASSUME Inv, Next, ProcessRequestFlag(0)
                 PROVE Inv'
                 OBVIOUS
                 
    \* Copy-pasted, may be a little inefficient
    <1>1 TypeOK'
        <2>1. TypeOK BY DEF Inv
        <2>2. turn' \in {0, 1} BY DEF Inv, TypeOK, ProcessRequestFlag
        <2>3. \A p \in {0, 1}: flag'[p] \in {TRUE, FALSE} 
            <3>1. \A p \in {0, 1}: flag[p] \in {TRUE, FALSE} BY DEF TypeOK, Inv
            <3>2. flag' = [flag EXCEPT ![0] = TRUE] BY DEF ProcessRequestFlag
            <3>3. flag' \in [{0,1} -> {TRUE, FALSE}] BY <3>2 DEF Inv, TypeOK
            <3>. QED BY <3>1, <3>2, <3>3 DEF Inv
        <2>4. processState' \in [{0,1} -> {"idle", "sentRequest", "waiting", "critical"}]
            <3>1. processState \in [{0,1} -> {"idle", "sentRequest", "waiting", "critical"}] BY DEF Inv, TypeOK, ProcessRequestFlag
            <3>2. processState' = [processState EXCEPT ![0] = "sentRequest"] BY DEF ProcessRequestFlag
            <3>3. processState' \in [{0,1} -> {"idle", "sentRequest", "waiting", "critical"}] BY <3>2 DEF Inv, TypeOK
            <3>. QED BY <3>1, <3>2, <3>3 DEF Inv
        <2>. QED BY <2>1, <2>2, <2>3, <2>4 DEF Inv, TypeOK, ProcessRequestFlag
    
        
    <1>2 MutualExclusion'
        <2>1 processState'[0] # "critical" BY DEF ProcessRequestFlag
        <2>. QED BY <2>1 DEF MutualExclusion
    
    <1>3 I'
        <2>1 SUFFICES ASSUME NEW p \in {0, 1}, NEW q \in {0, 1}, (p#q /\ processState[p] = "critical")'
                      PROVE (flag[q] = FALSE \/ turn = p \/ processState[q] = "sentRequest")'
                      BY DEF I
                            
        \* Assuming we can convince TLAPS that universal instantiation works, it's probably easier to prove by contradiction                     
        <2>2 SUFFICES ASSUME ~((flag[q] = FALSE \/ turn = p \/ processState[q] = "sentRequest")')
                      PROVE FALSE
                      OBVIOUS
                      
        <2>3 flag'[q] # FALSE /\ turn' # p /\ processState'[q] # "sentRequest" BY <2>2
        <2>4 flag'[q] = TRUE BY <1>1, <2>3 DEF TypeOK
        <2>5 p # q BY <2>1
        <2>6 turn' = q BY <1>1, <2>3, <2>5 DEF TypeOK
        <2>7 processState'[q] \in {"idle", "waiting", "critical"} BY <1>1, <2>3 DEF TypeOK
        <2>8 processState'[q] = "idle" \/ processState'[q] = "waiting" \/ processState'[q] = "critical" BY <2>7
        
        \* case for each processState value?
        <2>a CASE processState'[q] = "idle"
            <3>1 q = 0 \/ q = 1 BY DEF Inv, TypeOK
            <3>a CASE q = 0
                <4>1 processState' = [processState EXCEPT ![0] = "sentRequest"] BY DEF ProcessRequestFlag
                <4>2 processState' = [processState EXCEPT ![q] = "sentRequest"] BY <3>a, <4>1
                <4>3 q \in {0, 1} BY <3>1
                <4>4 processState'[q] = "sentRequest" BY <1>1, <4>2, <4>3 DEF TypeOK
                <4>. QED BY <2>a, <4>4
                
            <3>b CASE q = 1
                <4>1 p = 0 BY <1>1, <2>5, <3>b DEF TypeOK
                <4>2 processState'[p] = "critical" BY <2>1
                <4>4 processState' = [processState EXCEPT ![p] = "sentRequest"] BY <1>1, <4>1 DEF ProcessRequestFlag, TypeOK
                <4>5 processState'[p] = "sentRequest" BY <1>1, <4>4 DEF TypeOK
                
                <4>. QED BY <4>2, <4>5
                
            <3>. QED BY <3>a, <3>b
        
        <2>b CASE processState'[q] = "waiting"
            <3>1 q = 0 \/ q = 1 BY DEF Inv, TypeOK
            <3>a CASE q = 0
                <4>1 processState' = [processState EXCEPT ![0] = "sentRequest"] BY DEF ProcessRequestFlag
                <4>2 processState' = [processState EXCEPT ![q] = "sentRequest"] BY <3>a, <4>1
                <4>3 q \in {0, 1} BY <3>1
                <4>4 processState'[q] = "sentRequest" BY <1>1, <4>2, <4>3 DEF TypeOK
                <4>. QED BY <2>b, <4>4
                
                
                
            \* INCOMPLETE. <3>b NEEDED
            <3>b CASE q = 1
                <4>1 p = 0 BY <1>1, <2>5, <3>b DEF TypeOK
                <4>2 processState'[p] = "critical" BY <2>1
                <4>4 processState' = [processState EXCEPT ![p] = "sentRequest"] BY <1>1, <4>1 DEF ProcessRequestFlag, TypeOK
                <4>5 processState'[p] = "sentRequest" BY <1>1, <4>4 DEF TypeOK
                
                <4>. QED BY <4>2, <4>5
            
            (*
                <4>1 p = 0 BY <1>1, <2>5, <3>b DEF TypeOK
                <4>2 processState'[p] = "critical" BY <2>1
                <4>3 processState'[0] = "critical" BY <4>1, <4>2
                
                <4>4 processState[q] = "sentRequest"
                    <5>1 processState'[q] = "waiting" BY <2>b
                    <5>. QED BY <5>1 DEF Next, Process0, ProcessBeginWaiting
                <4>. QED
            *)    
                
            <3>. QED BY <3>a, <3>b
        
        <2>c CASE processState'[q] = "critical"
            <3>1 q = 0 \/ q = 1 BY DEF Inv, TypeOK
            <3>a CASE q = 0
                <4>1 processState' = [processState EXCEPT ![0] = "sentRequest"] BY DEF ProcessRequestFlag
                <4>2 processState' = [processState EXCEPT ![q] = "sentRequest"] BY <3>a, <4>1
                <4>3 q \in {0, 1} BY <3>1
                <4>4 processState'[q] = "sentRequest" BY <1>1, <4>2, <4>3 DEF TypeOK
                <4>. QED BY <2>c, <4>4
            
            <3>b CASE q = 1
                <4>1 p = 0 BY <1>1, <2>5, <3>b DEF TypeOK
                <4>2 processState'[p] = "critical" BY <2>1
                <4>3 processState'[q] = "critical" BY <2>c
                <4>5 processState'[0] = "critical" BY <4>1, <4>2
                <4>6 processState'[1] = "critical" BY <3>b, <4>3
                <4>. QED BY <1>2, <4>5, <4>6 DEF MutualExclusion
            
            <3>. QED BY <3>a, <3>b
        
        <2>. QED BY <2>7, <2>a, <2>b, <2>c DEF I

    
    <1>. QED BY <1>1, <1>2, <1>3 DEF Inv
    
THEOREM PBWInduction0 == Inv /\ Next /\ ProcessBeginWaiting(0) => Inv'
    <1> SUFFICES ASSUME Inv, Next, ProcessBeginWaiting(0)
                 PROVE Inv'
                 OBVIOUS
                 
    <1>1 TypeOK'
        <2>1. TypeOK BY DEF Inv
        <2>2. turn' \in {0, 1} BY DEF Inv, TypeOK, ProcessBeginWaiting
        <2>3. \A p \in {0, 1}: flag'[p] \in {TRUE, FALSE} 
            <3>1. \A p \in {0, 1}: flag[p] \in {TRUE, FALSE} BY DEF TypeOK, Inv
            <3>2. flag' = flag BY DEF ProcessBeginWaiting
            <3>3. flag' \in [{0,1} -> {TRUE, FALSE}] BY <3>2 DEF Inv, TypeOK
            <3>. QED BY <3>1, <3>2, <3>3 DEF Inv
        <2>4. processState' \in [{0,1} -> {"idle", "sentRequest", "waiting", "critical"}]
            <3>1. processState \in [{0,1} -> {"idle", "sentRequest", "waiting", "critical"}] BY DEF Inv, TypeOK, ProcessBeginWaiting
            <3>2. processState' = [processState EXCEPT ![0] = "waiting"] BY DEF ProcessBeginWaiting
            <3>3. processState' \in [{0,1} -> {"idle", "sentRequest", "waiting", "critical"}] BY <3>2 DEF Inv, TypeOK
            <3>. QED BY <3>1, <3>2, <3>3 DEF Inv
        <2>. QED BY <2>1, <2>2, <2>3, <2>4 DEF Inv, TypeOK, ProcessBeginWaiting
        
    <1>2 MutualExclusion'
        <2>1 processState'[0] # "critical" BY DEF ProcessBeginWaiting
        <2>. QED BY <2>1 DEF MutualExclusion
    
    <1>3 I'
    
    <1>. QED BY <1>1, <1>2, <1>3 DEF Inv
    
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
\* Last modified Fri May 30 15:32:28 EDT 2025 by johnnguyen
\* Created Fri May 30 09:25:52 EDT 2025 by johnnguyen
