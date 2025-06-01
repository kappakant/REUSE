--------------------------- MODULE PetersonLemmas ---------------------------
EXTENDS Peterson

\* Ok, so we're on the right track I think. Surely that nagging case isn't going to be super punishing.
\* Ian seemed to think that proof by contradiction was easier
\* Use NEW keyword to make it a bit more generalizable for TwoCommit
THEOREM PRFInduction0 == Inv /\ ProcessRequestFlag(0) => Inv'
    <1> SUFFICES ASSUME Inv, ProcessRequestFlag(0)
                 PROVE Inv'
                 OBVIOUS
                 
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
                
                
                
            <3>b CASE q = 1
                <4>1 p = 0 BY <1>1, <2>5, <3>b DEF TypeOK
                <4>2 processState'[p] = "critical" BY <2>1
                <4>4 processState' = [processState EXCEPT ![p] = "sentRequest"] BY <1>1, <4>1 DEF ProcessRequestFlag, TypeOK
                <4>5 processState'[p] = "sentRequest" BY <1>1, <4>4 DEF TypeOK
                
                <4>. QED BY <4>2, <4>5
                
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
    
THEOREM PBWInduction == Inv /\ ProcessBeginWaiting(0) => Inv'

    <1> SUFFICES ASSUME Inv, ProcessBeginWaiting(0)
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
        <2>1 SUFFICES ASSUME NEW p \in {0, 1}, NEW q \in {0, 1}, (p#q /\ processState[p] = "critical")'
                      PROVE (flag[q] = FALSE \/ turn = p \/ processState[q] = "sentRequest")'
                      BY DEF I
                                               
        <2>2 SUFFICES ASSUME ~((flag[q] = FALSE \/ turn = p \/ processState[q] = "sentRequest")')
                      PROVE FALSE
                      OBVIOUS
                      
        <2>3 flag'[q] # FALSE /\ turn' # p /\ processState'[q] # "sentRequest" BY <2>2
        <2>4 flag'[q] = TRUE BY <1>1, <2>3 DEF TypeOK
        <2>5 p # q BY <2>1
        <2>6 turn' = q BY <1>1, <2>3, <2>5 DEF TypeOK
        <2>7 processState'[q] \in {"idle", "waiting", "critical"} BY <1>1, <2>3 DEF TypeOK
        <2>8 processState'[q] = "idle" \/ processState'[q] = "waiting" \/ processState'[q] = "critical" BY <2>7
        
        <2>a CASE processState'[q] = "idle"
            <3>1 q = 0 \/ q = 1 BY DEF Inv, TypeOK
            <3>a CASE q = 0
                <4>1 processState' = [processState EXCEPT ![0] = "waiting"] BY DEF ProcessBeginWaiting
                <4>2 processState' = [processState EXCEPT ![q] = "waiting"] BY <3>a, <4>1
                <4>3 q \in {0, 1} BY <3>1
                <4>4 processState'[q] = "waiting" BY <1>1, <4>2, <4>3 DEF TypeOK
                <4>. QED BY <2>a, <4>4
                
            <3>b CASE q = 1
                <4>1 p = 0 BY <1>1, <2>5, <3>b DEF TypeOK
                <4>2 processState'[p] = "critical" BY <2>1
                <4>4 processState' = [processState EXCEPT ![p] = "waiting"] BY <1>1, <4>1 DEF ProcessBeginWaiting, TypeOK
                <4>5 processState'[p] = "waiting" BY <1>1, <4>4 DEF TypeOK
                
                <4>. QED BY <4>2, <4>5
                
            <3>. QED BY <3>a, <3>b
        
        <2>b CASE processState'[q] = "waiting"
            <3>1 q = 0 \/ q = 1 BY DEF Inv, TypeOK
            <3>a CASE q = 0
                <4>3 turn' = 1 BY DEF ProcessBeginWaiting
                <4>4 turn' = 0 BY <2>6, <3>a
                
                <4>. QED BY <4>3, <4>4
                
                
                
            <3>b CASE q = 1
                <4>1 p = 0 BY <1>1, <2>5, <3>b DEF TypeOK
                <4>2 processState'[p] = "critical" BY <2>1
                <4>4 processState' = [processState EXCEPT ![p] = "waiting"] BY <1>1, <4>1 DEF ProcessBeginWaiting, TypeOK
                <4>5 processState'[p] = "waiting" BY <1>1, <4>4 DEF TypeOK
                
                <4>. QED BY <4>2, <4>5
                
            <3>. QED BY <3>a, <3>b
        
        <2>c CASE processState'[q] = "critical"
            <3>1 q = 0 \/ q = 1 BY DEF Inv, TypeOK
            <3>a CASE q = 0
                <4>1 processState' = [processState EXCEPT ![0] = "waiting"] BY DEF ProcessBeginWaiting
                <4>2 processState' = [processState EXCEPT ![q] = "waiting"] BY <3>a, <4>1
                <4>3 q \in {0, 1} BY <3>1
                <4>4 processState'[q] = "waiting" BY <1>1, <4>2, <4>3 DEF TypeOK
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
    
THEOREM PEnCInduction0 == Inv /\ ProcessEnterCritical(0) => Inv'
    <1> SUFFICES ASSUME Inv, ProcessEnterCritical(0)
                 PROVE Inv'
                 OBVIOUS
                 
    <1>1 TypeOK'
        <2>1. TypeOK BY DEF Inv
        <2>2. turn' \in {0, 1} BY DEF Inv, TypeOK, ProcessEnterCritical
        <2>3. \A p \in {0, 1}: flag'[p] \in {TRUE, FALSE} 
            <3>1. \A p \in {0, 1}: flag[p] \in {TRUE, FALSE} BY DEF TypeOK, Inv
            <3>2. flag' = flag BY DEF ProcessEnterCritical
            <3>3. flag' \in [{0,1} -> {TRUE, FALSE}] BY <3>2 DEF Inv, TypeOK
            <3>. QED BY <3>1, <3>2, <3>3 DEF Inv
        <2>4. processState' \in [{0,1} -> {"idle", "sentRequest", "waiting", "critical"}]
            <3>1. processState \in [{0,1} -> {"idle", "sentRequest", "waiting", "critical"}] BY DEF Inv, TypeOK, ProcessEnterCritical
            <3>2. processState' = [processState EXCEPT ![0] = "critical"] BY DEF ProcessEnterCritical
            <3>3. processState' \in [{0,1} -> {"idle", "sentRequest", "waiting", "critical"}] BY <3>2 DEF Inv, TypeOK
            <3>. QED BY <3>1, <3>2, <3>3 DEF Inv
        <2>. QED BY <2>1, <2>2, <2>3, <2>4 DEF Inv, TypeOK, ProcessEnterCritical
    
    \* TODO
    <1>2 MutualExclusion'
        <2>1 SUFFICES ASSUME processState'[0] = "critical" /\ processState'[1] = "critical"
                     PROVE FALSE
                     BY DEF MutualExclusion
        <2>7 processState[0] = "waiting" BY DEF ProcessEnterCritical
        <2>8 flag[1] = FALSE \/ turn = 0 BY DEF ProcessEnterCritical
        
        <2>9 processState' = [processState EXCEPT ![0] = "critical"] BY DEF ProcessEnterCritical
        <2>10 processState[1] = "critical" BY <1>1, <2>1, <2>9 DEF TypeOK
        <2>11 flag[0] = FALSE \/ turn = 1 \/ processState[0] = "sentRequest" BY <2>10 DEF Inv, I
        
        <2>12 flag[0] = FALSE \/ turn = 1 BY <2>7, <2>11
        
        \* I method
        <2>13 flag'[1] = FALSE \/ turn' = 0 BY <2>8 DEF ProcessEnterCritical
        <2>14 flag'[0] = FALSE \/ turn' = 1 BY <2>12 DEF ProcessEnterCritical
        <2>15 I'
        <2>16 (0#1 /\ processState'[0] = "critical") => flag'[1] = FALSE \/ turn' = 0 \/ processState'[1] = "sentRequest" BY <2>15

        <2>. QED
    
    <1>3 I'
        <2>1 SUFFICES ASSUME NEW p \in {0, 1}, NEW q \in {0, 1}, (p#q /\ processState[p] = "critical")'
                      PROVE (flag[q] = FALSE \/ turn = p \/ processState[q] = "sentRequest")'
                      BY DEF I
                                               
        <2>2 SUFFICES ASSUME ~((flag[q] = FALSE \/ turn = p \/ processState[q] = "sentRequest")')
                      PROVE FALSE
                      OBVIOUS
                      
        <2>3 flag'[q] # FALSE /\ turn' # p /\ processState'[q] # "sentRequest" BY <2>2
        <2>4 flag'[q] = TRUE BY <1>1, <2>3 DEF TypeOK
        <2>5 p # q BY <2>1
        <2>6 turn' = q BY <1>1, <2>3, <2>5 DEF TypeOK
        <2>7 processState'[q] \in {"idle", "waiting", "critical"} BY <1>1, <2>3 DEF TypeOK
        <2>8 processState'[q] = "idle" \/ processState'[q] = "waiting" \/ processState'[q] = "critical" BY <2>7
        
        <2>a CASE processState'[q] = "idle"
            <3>1 q = 0 \/ q = 1 BY DEF Inv, TypeOK
            <3>a CASE q = 0
                <4>1 processState' = [processState EXCEPT ![0] = "critical"] BY DEF ProcessEnterCritical
                <4>2 processState' = [processState EXCEPT ![q] = "critical"] BY <3>a, <4>1
                <4>3 q \in {0, 1} BY <3>1
                <4>4 processState'[q] = "critical" BY <1>1, <4>2, <4>3 DEF TypeOK
                <4>. QED BY <2>a, <4>4
            
            <3>b CASE q = 1
                <4>1 flag'[1] = FALSE \/ turn = 0 BY DEF ProcessEnterCritical
                <4>a CASE flag'[1] = FALSE
                    <5>. QED BY <2>4, <3>b, <4>a
                <4>b CASE turn = 0
                    <5>1. turn' = 0 BY <4>b DEF ProcessEnterCritical
                    <5>2. turn' = 1 BY <2>6, <3>b
                    <5>. QED BY <5>1, <5>2
               
                <4>. QED BY <4>1, <4>a, <4>b
            <3>. QED BY <3>1, <3>a, <3>b
        
        <2>b CASE processState'[q] = "waiting"
            <3>1 q = 0 \/ q = 1 BY DEF Inv, TypeOK
            <3>a CASE q = 0
                <4>1 processState' = [processState EXCEPT ![0] = "critical"] BY DEF ProcessEnterCritical
                <4>2 processState' = [processState EXCEPT ![q] = "critical"] BY <3>a, <4>1
                <4>3 q \in {0, 1} BY <3>1
                <4>4 processState'[q] = "critical" BY <1>1, <4>2, <4>3 DEF TypeOK
                <4>. QED BY <2>b, <4>4
                
                
            <3>b CASE q = 1
                <4>1 flag'[1] = FALSE \/ turn = 0 BY DEF ProcessEnterCritical
                <4>a CASE flag'[1] = FALSE
                    <5>. QED BY <2>4, <3>b, <4>a
                <4>b CASE turn = 0
                    <5>1. turn' = 0 BY <4>b DEF ProcessEnterCritical
                    <5>2. turn' = 1 BY <2>6, <3>b
                    <5>. QED BY <5>1, <5>2
               
                <4>. QED BY <4>1, <4>a, <4>b
                
            <3>. QED BY <3>a, <3>b
        
        <2>c CASE processState'[q] = "critical"
            <3>1 q = 0 \/ q = 1 BY DEF Inv, TypeOK
            <3>a CASE q = 0
                <4>1 p = 1 BY <1>1, <2>5, <3>a DEF TypeOK
                <4>2 processState'[p] = "critical" BY <2>1
                <4>3 processState'[q] = "critical" BY <2>c
                <4>5 processState'[0] = "critical" BY <3>a, <4>3
                <4>6 processState'[1] = "critical" BY <4>1, <4>2
                <4>. QED BY <1>2, <4>5, <4>6 DEF MutualExclusion
            
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
    
THEOREM PExCInduction0 == Inv /\ Next /\ ProcessExitCritical(0) => Inv'
    <1> SUFFICES ASSUME Inv, Next, ProcessExitCritical(0)
                 PROVE Inv'
                 OBVIOUS
                 
    <1>1 TypeOK'
        <2>1. TypeOK BY DEF Inv
        <2>2. turn' \in {0, 1} BY DEF Inv, TypeOK, ProcessExitCritical
        <2>3. \A p \in {0, 1}: flag'[p] \in {TRUE, FALSE} 
            <3>1. \A p \in {0, 1}: flag[p] \in {TRUE, FALSE} BY DEF TypeOK, Inv
            <3>2. flag' = [flag EXCEPT ![0] = FALSE] BY DEF ProcessExitCritical
            <3>3. flag' \in [{0,1} -> {TRUE, FALSE}] BY <3>2 DEF Inv, TypeOK
            <3>. QED BY <3>1, <3>2, <3>3 DEF Inv
        <2>4. processState' \in [{0,1} -> {"idle", "sentRequest", "waiting", "critical"}]
            <3>1. processState \in [{0,1} -> {"idle", "sentRequest", "waiting", "critical"}] BY DEF Inv, TypeOK, ProcessExitCritical
            <3>2. processState' = [processState EXCEPT ![0] = "idle"] BY DEF ProcessExitCritical
            <3>3. processState' \in [{0,1} -> {"idle", "sentRequest", "waiting", "critical"}] BY <3>2 DEF Inv, TypeOK
            <3>. QED BY <3>1, <3>2, <3>3 DEF Inv
        <2>. QED BY <2>1, <2>2, <2>3, <2>4 DEF Inv, TypeOK, ProcessExitCritical
        
    <1>2 MutualExclusion'
        <2>1 processState' = [processState EXCEPT ![0] = "idle"] BY DEF ProcessExitCritical
        <2>2 processState'[0] = "idle" BY <1>1, <2>1 DEF TypeOK
        <2>. QED BY <2>2 DEF MutualExclusion
        
    <1>3 I'
        <2>1 SUFFICES ASSUME NEW p \in {0, 1}, NEW q \in {0, 1}, (p#q /\ processState[p] = "critical")'
                      PROVE (flag[q] = FALSE \/ turn = p \/ processState[q] = "sentRequest")'
                      BY DEF I
                                               
        <2>2 SUFFICES ASSUME ~((flag[q] = FALSE \/ turn = p \/ processState[q] = "sentRequest")')
                      PROVE FALSE
                      OBVIOUS
                      
        <2>3 flag'[q] # FALSE /\ turn' # p /\ processState'[q] # "sentRequest" BY <2>2
        <2>4 flag'[q] = TRUE BY <1>1, <2>3 DEF TypeOK
        <2>5 p # q BY <2>1
        <2>6 turn' = q BY <1>1, <2>3, <2>5 DEF TypeOK
        <2>7 processState'[q] \in {"idle", "waiting", "critical"} BY <1>1, <2>3 DEF TypeOK
        <2>8 processState'[q] = "idle" \/ processState'[q] = "waiting" \/ processState'[q] = "critical" BY <2>7
        
        <2>a CASE processState'[q] = "idle"
            <3>1 q = 0 \/ q = 1 BY DEF Inv, TypeOK
            <3>a CASE q = 0
                <4>1 processState'[p] = "critical" BY <2>1
                <4>2 processState' = [processState EXCEPT ![0] = "idle"] BY DEF ProcessExitCritical
                <4>3 processState'[1] = "critical" BY <1>1, <2>5, <3>a, <4>1 DEF TypeOK
                <4>4 processState[1] = "critical" BY <4>2, <4>3
                <4>5 processState[0] = "critical" BY DEF ProcessExitCritical
                <4>. QED BY <4>4, <4>5 DEF Inv, MutualExclusion
            
            <3>b CASE q = 1
                <4>1 p = 0 BY <1>1, <2>5, <3>b DEF TypeOK
                <4>2 processState'[0] = "idle" BY <1>1 DEF ProcessExitCritical, TypeOK
                <4>3 processState'[p] = "idle" BY <4>1, <4>2
                <4>. QED BY <2>1, <4>3
            <3>. QED BY <3>1, <3>a, <3>b
        
        <2>b CASE processState'[q] = "waiting"
            <3>1 q = 0 \/ q = 1 BY DEF Inv, TypeOK
            <3>a CASE q = 0
                <4>1 processState' = [processState EXCEPT ![0] = "idle"] BY DEF ProcessExitCritical
                <4>2 processState' = [processState EXCEPT ![q] = "idle"] BY <3>a, <4>1
                <4>3 q \in {0, 1} BY <3>1
                <4>4 processState'[q] = "idle" BY <1>1, <4>2, <4>3 DEF TypeOK
                <4>. QED BY <2>b, <4>4
                
                
            <3>b CASE q = 1
                <4>1 p = 0 BY <1>1, <2>5, <3>b DEF TypeOK
                <4>2 processState' = [processState EXCEPT ![0] = "idle"] BY DEF ProcessExitCritical
                <4>3 processState'[p] = "idle" BY <1>1, <4>1, <4>2 DEF TypeOK
                <4>. QED BY <2>1, <4>3
                
            <3>. QED BY <3>a, <3>b
        
        <2>c CASE processState'[q] = "critical"
            <3>1 q = 0 \/ q = 1 BY DEF Inv, TypeOK
            <3>a CASE q = 0
                <4>1 p = 1 BY <1>1, <2>5, <3>a DEF TypeOK
                <4>2 processState'[p] = "critical" BY <2>1
                <4>3 processState'[q] = "critical" BY <2>c
                <4>5 processState'[0] = "critical" BY <3>a, <4>3
                <4>6 processState'[1] = "critical" BY <4>1, <4>2
                <4>. QED BY <1>2, <4>5, <4>6 DEF MutualExclusion
            
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
\* Last modified Sat May 31 19:17:50 EDT 2025 by johnnguyen
\* Created Fri May 30 09:25:52 EDT 2025 by johnnguyen
