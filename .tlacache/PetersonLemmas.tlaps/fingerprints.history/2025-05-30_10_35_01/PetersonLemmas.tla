--------------------------- MODULE PetersonLemmas ---------------------------
EXTENDS Peterson

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
    
    <1>2 I'
        <2> PICK p \in {0,1}: TRUE OBVIOUS
        <2> PICK q \in {0,1}: TRUE OBVIOUS
        <2> SUFFICES ASSUME (p#q /\ processState[p] = "critical")'
                             PROVE (flag[q] = FALSE \/ turn = p \/ processState[q] = "sentRequest")'
                             BY DEF I
                             
        <2>1 SUFFICES ASSUME ~((flag[q] = FALSE \/ turn = p \/ processState[q] = "sentRequest")')
                      PROVE FALSE
                      OBVIOUS
                     
        <2>2 flag'[q] # FALSE /\ turn' # p /\ processState'[q] # "sentRequest" BY <2>1
        <2>3 flag'[q] = TRUE BY <2>2
        
        <2>. QED BY <2>1 DEF I
    
    <1>3 MutualExclusion'
        <2>1 processState'[0] # "critical" BY DEF ProcessRequestFlag
        <2>. QED BY <2>1 DEF MutualExclusion
    
    <1>. QED BY <1>1, <1>2, <1>3 DEF Inv
    
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
\* Last modified Fri May 30 10:34:58 EDT 2025 by johnnguyen
\* Created Fri May 30 09:25:52 EDT 2025 by johnnguyen

THEOREM InductProperty == Inv /\ Next => Inv'
    <1> SUFFICES ASSUME Inv, Next
                 PROVE Inv'
                 OBVIOUS
    \*<1> USE DEF Inv, Next  
    <1>1 Process0 \/ Process1 
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

            <3>3. MutualExclusion'
                <4>1 processState'[0] # "critical" BY <2>a DEF ProcessRequestFlag \* BY <4>11
             
                <4>. QED BY <4>1 DEF MutualExclusion
                
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
                <4> PICK p \in {0,1}: TRUE OBVIOUS
                <4> PICK q \in {0,1}: TRUE OBVIOUS
                <4>1 SUFFICES ASSUME (p#q /\ processState[p] = "critical")'
                             PROVE (flag[q] = FALSE \/ turn = p \/ processState[q] = "sentRequest")'
                <4>2 processState'[p] = "critical" BY <4>1
                <4>3 processState[0] = "waiting" \* BY <2>b DEF ProcessBeginWaiting
                <4>4 processState'[0] # "critical" BY <2>b DEF ProcessBeginWaiting 
                <4>. QED

            <3>3 MutualExclusion'
                <4>1 processState'[0] # "critical" BY <2>b DEF ProcessBeginWaiting 
                <4>. QED BY <4>1 DEF MutualExclusion
            
            <3>. QED BY <3>1, <3>2, <3>3 DEF Inv
        <2>c CASE ProcessEnterCritical(0)
            <3>1 TypeOK'
                <4>1. TypeOK BY DEF Inv
                <4>2. turn' \in {0, 1} BY <2>c DEF Inv, TypeOK, ProcessEnterCritical
                <4>3. \A p \in {0, 1}: flag'[p] \in {TRUE, FALSE} 
                    <5>1. \A p \in {0, 1}: flag[p] \in {TRUE, FALSE} BY <2>c DEF TypeOK, Inv
                    <5>2. flag' = flag BY <2>c DEF ProcessEnterCritical
                    <5>3. flag' \in [{0,1} -> {TRUE, FALSE}] BY <5>2 DEF Inv, TypeOK
                    <5>. QED BY <5>1, <5>2, <5>3 DEF Inv
                <4>4. processState' \in [{0,1} -> {"idle", "sentRequest", "waiting", "critical"}]
                    <5>1. processState \in [{0,1} -> {"idle", "sentRequest", "waiting", "critical"}] BY <2>c DEF Inv, TypeOK, ProcessEnterCritical
                    <5>2. processState' = [processState EXCEPT ![0] = "critical"] BY <2>c DEF ProcessEnterCritical
                    <5>3. processState' \in [{0,1} -> {"idle", "sentRequest", "waiting", "critical"}] BY <5>2 DEF Inv, TypeOK
                    <5>. QED BY <5>1, <5>2, <5>3 DEF Inv
                <4>. QED BY <2>c, <4>1, <4>2, <4>3, <4>4 DEF Inv, TypeOK, ProcessEnterCritical
                
             <3>2 I'
             
             \* Use I to guarantee that other side is not critical
             <3>3 MutualExclusion'
                <4>1 processState' = [processState EXCEPT ![0] = "idle"] BY <2>c DEF ProcessEnterCritical
                <4>2 processState'[0] # "critical" BY <2>c DEF ProcessEnterCritical
                <4>. QED BY <4>1 DEF MutualExclusion   
             <3>. QED
        <2>d CASE ProcessExitCritical(0)
            <3>1 TypeOK'
                <4>1. TypeOK BY DEF Inv
                <4>2. turn' \in {0, 1} BY <2>d DEF Inv, TypeOK, ProcessExitCritical
                <4>3. \A p \in {0, 1}: flag'[p] \in {TRUE, FALSE} 
                    <5>1. \A p \in {0, 1}: flag[p] \in {TRUE, FALSE} BY <2>d DEF TypeOK, Inv
                    <5>2. flag' = [flag EXCEPT ![0] = FALSE] BY <2>d DEF ProcessExitCritical
                    <5>3. flag' \in [{0,1} -> {TRUE, FALSE}] BY <5>2 DEF Inv, TypeOK
                    <5>. QED BY <5>1, <5>2, <5>3 DEF Inv
                <4>4. processState' \in [{0,1} -> {"idle", "sentRequest", "waiting", "critical"}]
                    <5>1. processState \in [{0,1} -> {"idle", "sentRequest", "waiting", "critical"}] BY <2>d DEF Inv, TypeOK, ProcessExitCritical
                    <5>2. processState' = [processState EXCEPT ![0] = "idle"] BY <2>d DEF ProcessExitCritical
                    <5>3. processState' \in [{0,1} -> {"idle", "sentRequest", "waiting", "critical"}] BY <5>2 DEF Inv, TypeOK
                    <5>. QED BY <5>1, <5>2, <5>3 DEF Inv
                <4>. QED BY <2>d, <4>1, <4>2, <4>3, <4>4 DEF Inv, TypeOK, ProcessExitCritical
            
            <3>2 I'
            
            \* Also, mutualexclusion went back to not working
            <3>3 MutualExclusion'
                <4>1 processState'[0] # "critical" BY <2>d DEF ProcessExitCritical
                <4>. QED BY <4>1 DEF MutualExclusion   
            <3>. QED
        <2> QED BY <2>1, <2>a, <2>b, <2>c, <2>d DEF ProcessRequestFlag, ProcessBeginWaiting, ProcessEnterCritical, ProcessExitCritical, TypeOK, MutualExclusion
        
    \* Copy-paste Process0 when done. Do Repeat Yourself.  
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
