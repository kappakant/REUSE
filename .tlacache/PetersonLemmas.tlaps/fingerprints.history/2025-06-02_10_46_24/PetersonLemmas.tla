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
        <2>1 SUFFICES ASSUME NEW p \in {0, 1}, NEW q \in {0, 1}
                      PROVE (critReqs(p, q) /\ requestReqs(p, q) /\ waitReqs(p, q))'
                      BY DEF I
                                               
        <2>a critReqs(p, q)'
            \* Nothing contradictory about this
            <3>1 SUFFICES ASSUME p#q /\ processState'[p] = "critical"
                          PROVE (flag'[q] = FALSE \/ turn' = p \/ processState'[q] = "sentRequest") /\ flag'[p] = TRUE
                          BY DEF critReqs
                          
            <3>2 (p = 0 /\ q = 1) \/ (p = 1 /\ q = 0) BY <1>1, <3>1 DEF TypeOK 
                   
            <3>a CASE p = 0 /\ q = 1
                <4>1 processState' = [processState EXCEPT ![0] = "sentRequest"] BY DEF ProcessRequestFlag
                <4>2 processState'[p] = "sentRequest" BY <1>1, <3>a, <4>1 DEF TypeOK \* surprisingly smart
                <4>. QED BY <3>1, <4>2
                
            <3>b CASE p = 1 /\ q = 0
                <4>1 processState' = [processState EXCEPT ![0] = "sentRequest"] BY DEF ProcessRequestFlag
                <4>2 processState'[0] = "sentRequest" BY <1>1, <4>1 DEF TypeOK
                <4>3 processState'[q] = "sentRequest" BY <3>b, <4>2
                
                <4>4 processState'[1] = "critical" BY <3>1, <3>b
                <4>5 processState[1] = "critical" BY <4>4 DEF ProcessRequestFlag
                <4>7 flag[1] = TRUE BY <4>5 DEF Inv, I, critReqs
                <4>8 flag' = [flag EXCEPT ![0] = TRUE] BY DEF ProcessRequestFlag
                <4>9 flag'[1] = TRUE BY <1>1, <4>7, <4>8 DEF TypeOK
                <4>10 flag'[p] = TRUE BY <3>b, <4>9
                
                <4>. QED BY <4>3, <4>10

            <3>. QED BY <3>2, <3>a, <3>b
        
        <2>b requestReqs(p, q)'
            <3>1 SUFFICES ASSUME p#q /\ processState'[p] = "sentRequest"
                          PROVE flag'[p] = TRUE
                          BY DEF requestReqs 
            <3>2 (p = 0 /\ q = 1) \/ (p = 1 /\ q = 0) BY <1>1, <3>1 DEF TypeOK 
                   
            <3>a CASE p = 0 /\ q = 1
                <4>1 flag' = [flag EXCEPT ![0] = TRUE] BY DEF ProcessRequestFlag
                <4>2 flag'[0] = TRUE BY <1>1, <4>1 DEF TypeOK
                <4>. QED BY <3>a, <4>2
                
            <3>b CASE p = 1 /\ q = 0
                <4>1 processState' = [processState EXCEPT ![0] = "sentRequest"] BY DEF ProcessRequestFlag
                <4>2 processState[1] = "sentRequest" BY <1>1, <3>1, <4>1, <3>b DEF TypeOK
                
                <4>6 flag[p] = TRUE BY <3>b, <4>2 DEF Inv, I, requestReqs
                <4>7 flag'[p] = TRUE BY <4>6 DEF ProcessRequestFlag
                <4>. QED BY <4>7

            <3>. QED BY <3>2, <3>a, <3>b
        
        <2>c waitReqs(p, q)'
            <3>1 SUFFICES ASSUME p#q /\ processState'[p] = "waiting"
                          PROVE flag'[p] = TRUE
                          BY DEF waitReqs 
            <3>2 (p = 0 /\ q = 1) \/ (p = 1 /\ q = 0) BY <1>1, <3>1 DEF TypeOK 
                   
            <3>a CASE p = 0 /\ q = 1
                <4>1 processState'[p] = "waiting" BY <3>1
                <4>2 processState' = [processState EXCEPT ![0] = "sentRequest"] BY DEF ProcessRequestFlag
                <4>3 processState'[0] = "sentRequest" BY <1>1, <4>2 DEF TypeOK
                <4>4 processState'[p] = "sentRequest" BY <3>a, <4>3
                <4>. QED BY <3>1, <4>4
                
            <3>b CASE p = 1 /\ q = 0
                <4>1 processState' = [processState EXCEPT ![0] = "sentRequest"] BY DEF ProcessRequestFlag
                <4>2 processState[1] = "waiting" BY <1>1, <3>1, <4>1, <3>b DEF TypeOK
                <4>6 flag[p] = TRUE BY <3>b, <4>2 DEF Inv, I, waitReqs
                <4>7 flag'[p] = TRUE BY <4>6 DEF ProcessRequestFlag
                <4>. QED BY <4>7

            <3>. QED BY <3>2, <3>a, <3>b
        
        <2>. QED BY <2>1, <2>a, <2>b, <2>c DEF I

    
    <1>. QED BY <1>1, <1>2, <1>3 DEF Inv
    
THEOREM PBWInduction0 == Inv /\ ProcessBeginWaiting(0) => Inv'

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
        <2>1 SUFFICES ASSUME NEW p \in {0, 1}, NEW q \in {0, 1}
                      PROVE (critReqs(p, q) /\ requestReqs(p, q) /\ waitReqs(p, q))'
                      BY DEF I
                                               
        <2>a critReqs(p, q)'
            <3>1 SUFFICES ASSUME p#q /\ processState'[p] = "critical"
                          PROVE (flag'[q] = FALSE \/ turn' = p \/ processState'[p] = "sentRequest") /\ flag'[p] = TRUE
                          BY DEF critReqs
                          
            <3>2 (p = 0 /\ q = 1) \/ (p = 1 /\ q = 0) BY <1>1, <3>1 DEF TypeOK 
                   
            <3>a CASE p = 0 /\ q = 1
                <4>1 processState' = [processState EXCEPT ![0] = "waiting"] BY DEF ProcessBeginWaiting
                <4>2 processState'[p] = "waiting" BY <1>1, <3>a, <4>1 DEF TypeOK
                <4>. QED BY <3>1, <4>2
                
            <3>b CASE p = 1 /\ q = 0
                <4>1 processState' = [processState EXCEPT ![0] = "waiting"] BY DEF ProcessBeginWaiting
                <4>2 processState[1] = "critical" BY <1>1, <3>1, <4>1, <3>b DEF TypeOK
                <4>3 processState[0] = "sentRequest" BY DEF ProcessBeginWaiting
                <4>4 turn' = 1 BY DEF ProcessBeginWaiting
                <4>5 turn' = p BY <3>b, <4>4
                <4>6 flag[p] = TRUE BY <3>b, <4>2 DEF Inv, I, critReqs
                <4>7 flag'[p] = TRUE BY <4>6 DEF ProcessBeginWaiting
                <4>. QED BY <4>5, <4>7

            <3>. QED BY <3>2, <3>a, <3>b
        
        <2>b requestReqs(p, q)'
            <3>1 SUFFICES ASSUME p#q /\ processState'[p] = "sentRequest"
                          PROVE flag'[p] = TRUE
                          BY DEF requestReqs 
            <3>2 (p = 0 /\ q = 1) \/ (p = 1 /\ q = 0) BY <1>1, <3>1 DEF TypeOK 
                   
            <3>a CASE p = 0 /\ q = 1
                <4>1 processState' = [processState EXCEPT ![0] = "waiting"] BY DEF ProcessBeginWaiting
                <4>2 processState'[p] = "waiting" BY <1>1, <3>a, <4>1 DEF TypeOK
                <4>. QED BY <3>1, <4>2
                
            <3>b CASE p = 1 /\ q = 0
                <4>1 processState' = [processState EXCEPT ![0] = "waiting"] BY DEF ProcessBeginWaiting
                <4>2 processState[1] = "sentRequest" BY <1>1, <3>1, <4>1, <3>b DEF TypeOK
                <4>3 processState[0] = "sentRequest" BY DEF ProcessBeginWaiting
                <4>4 turn' = 1 BY DEF ProcessBeginWaiting
                <4>5 turn' = p BY <3>b, <4>4
                <4>6 flag[p] = TRUE BY <3>b, <4>2 DEF Inv, I, requestReqs
                <4>7 flag'[p] = TRUE BY <4>6 DEF ProcessBeginWaiting
                <4>. QED BY <4>5, <4>7

            <3>. QED BY <3>2, <3>a, <3>b
        
        <2>c waitReqs(p, q)'
            <3>1 SUFFICES ASSUME p#q /\ processState'[p] = "waiting"
                          PROVE flag'[p] = TRUE
                          BY DEF waitReqs 
            <3>2 (p = 0 /\ q = 1) \/ (p = 1 /\ q = 0) BY <1>1, <3>1 DEF TypeOK 
                   
            <3>a CASE p = 0 /\ q = 1
                <4>1 processState[0] = "sentRequest" BY DEF ProcessBeginWaiting
                <4>2 flag[0] = TRUE BY <4>1 DEF Inv, I, requestReqs
                <4>3 flag'[0] = TRUE BY <4>2 DEF ProcessBeginWaiting
                <4>4 flag'[p] = TRUE BY <3>a, <4>3 
                <4>. QED BY <4>4
                
            <3>b CASE p = 1 /\ q = 0
                <4>1 processState' = [processState EXCEPT ![0] = "waiting"] BY DEF ProcessBeginWaiting
                <4>2 processState[1] = "waiting" BY <1>1, <3>1, <4>1, <3>b DEF TypeOK
                <4>3 processState[0] = "sentRequest" BY DEF ProcessBeginWaiting
                <4>4 turn' = 1 BY DEF ProcessBeginWaiting
                <4>5 turn' = p BY <3>b, <4>4
                <4>6 flag[p] = TRUE BY <3>b, <4>2 DEF Inv, I, waitReqs
                <4>7 flag'[p] = TRUE BY <4>6 DEF ProcessBeginWaiting
                <4>. QED BY <4>5, <4>7

            <3>. QED BY <3>2, <3>a, <3>b
        
        <2>. QED BY <2>1, <2>a, <2>b, <2>c DEF I
    
    
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
    
    <1>2 MutualExclusion'
        <2>1 SUFFICES ASSUME processState'[0] = "critical" /\ processState'[1] = "critical"
                      PROVE FALSE
                      BY DEF MutualExclusion
                      
        <2>2 processState[0] = "waiting" BY DEF ProcessEnterCritical
        <2>3 flag[1] = FALSE \/ turn = 0 BY DEF ProcessEnterCritical
        
        <2>4 processState' = [processState EXCEPT ![0] = "critical"] BY DEF ProcessEnterCritical
        <2>5 processState[1] = "critical" BY <1>1, <2>1, <2>4 DEF TypeOK
        
        <2>6 (flag[0] = FALSE \/ turn = 1 \/ processState[0] = "sentRequest") BY <2>5 DEF Inv, I, critReqs
        <2>7 flag[0] = FALSE \/ turn = 1 BY <2>2, <2>6       
        <2>8 flag[0] = TRUE BY <2>2 DEF Inv, I, waitReqs
        <2>9 turn = 1 BY <2>7, <2>8
        
        <2>10 flag[1] = FALSE BY <2>3, <2>9
        <2>11 flag[1] = TRUE BY <2>5 DEF Inv, I, critReqs
        
        <2>. QED BY <2>10, <2>11
    
    <1>3 I'
        <2>1 SUFFICES ASSUME NEW p \in {0, 1}, NEW q \in {0, 1}
                      PROVE (critReqs(p, q) /\ requestReqs(p, q) /\ waitReqs(p, q))'
                      BY DEF I
        
        <2>a critReqs(p, q)'
            <3>1 SUFFICES ASSUME p#q /\ processState'[p] = "critical"
                          PROVE (flag'[q] = FALSE \/ turn' = p \/ processState'[q] = "sentRequest") /\ flag'[p] = TRUE
                          BY DEF critReqs
                          
            <3>2 (p = 0 /\ q = 1) \/ (p = 1 /\ q = 0) BY <1>1, <3>1 DEF TypeOK        
            <3>a CASE p = 0 /\ q = 1
                <4>1 processState[p] = "waiting" BY <3>a DEF ProcessEnterCritical
                <4>2 flag[p] = TRUE BY <4>1 DEF Inv, I, waitReqs
                <4>3 flag'[p] = TRUE BY <4>2 DEF ProcessEnterCritical
                
                <4>4 flag[1] = FALSE \/ turn = 0 BY DEF ProcessEnterCritical
                
                <4>a CASE flag[1] = FALSE
                    <5>1 flag'[1] = FALSE BY <4>a DEF ProcessEnterCritical
                    <5>2 flag'[q] = FALSE BY <3>a, <5>1
                    <5>. QED BY <4>3, <5>2
                    
                <4>b CASE turn = 0
                    <5>1 turn' = 0 BY <4>b DEF ProcessEnterCritical
                    <5>2 turn' = p BY <3>a, <5>1
                    <5>. QED BY <4>3, <5>2
                <4>. QED BY <4>4, <4>a, <4>b
            
            <3>b CASE p = 1 /\ q = 0
                <4>1 processState' = [processState EXCEPT ![0] = "critical"] BY DEF ProcessEnterCritical
                <4>2 processState[1] = "critical" BY <1>1, <3>1, <4>1, <3>b DEF TypeOK
                <4>3 processState[0] = "waiting" BY DEF ProcessEnterCritical
                
                <4>4 flag[0] = FALSE \/ turn = 1 \/ processState[0] = "sentRequest" BY <3>1, <4>2 DEF Inv, I, critReqs 
                <4>5 flag[0] = FALSE \/ turn = 1 BY <4>3, <4>4
                
                <4>a CASE flag[0] = FALSE
                    <5>1 flag[0] = TRUE BY <4>3 DEF Inv, I, waitReqs
                    <5>. QED BY <4>a, <5>1
                
                <4>b CASE turn = 1
                    <5>1 flag[1] = FALSE \/ turn = 0 BY DEF ProcessEnterCritical
                    <5>2 flag[1] = FALSE BY <4>b, <5>1
                    <5>3 flag[1] = TRUE BY <4>2 DEF Inv, I, critReqs 
                    <5>. QED BY <5>2, <5>3
                    
                <4>. QED BY <4>5, <4>a, <4>b
            <3>. QED BY <3>2, <3>a, <3>b
           
        <2>b requestReqs(p, q)'
            <3>1 SUFFICES ASSUME p#q /\ processState'[p] = "sentRequest"
                          PROVE flag'[p] = TRUE
                          BY DEF requestReqs
            <3>2 (p = 0 /\ q = 1) \/ (p = 1 /\ q = 0) BY <1>1, <3>1 DEF TypeOK
            
            <3>a CASE p = 0 /\ q = 1
                <4>1 processState' = [processState EXCEPT ![p] = "critical"] BY <3>a DEF ProcessEnterCritical
                
                <4>2 processState'[p] = "critical" BY <1>1, <3>a DEF TypeOK, ProcessEnterCritical
                <4>3 processState'[p] = "sentRequest" BY <3>1
                <4>. QED BY <4>2, <4>3
            
            <3>b CASE p = 1 /\ q = 0
                <4>1 processState' = [processState EXCEPT ![q] = "critical"] BY <3>b DEF ProcessEnterCritical
                <4>2 processState[p] = "sentRequest" BY <1>1, <3>1, <4>1 DEF TypeOK
                <4>3 flag[p] = TRUE BY <4>2 DEF Inv, I, requestReqs
                <4>4 flag'[p] = TRUE BY <4>3 DEF ProcessEnterCritical
                <4>. QED BY <4>4
            
            <3>. QED BY <3>2, <3>a, <3>b
            
        <2>c waitReqs(p, q)'
            <3>1 SUFFICES ASSUME p#q /\ processState'[p] = "waiting"
                          PROVE flag'[p] = TRUE
                          BY DEF waitReqs
            <3>2 (p = 0 /\ q = 1) \/ (p = 1 /\ q = 0) BY <1>1, <3>1 DEF TypeOK
            
            <3>a CASE p = 0 /\ q = 1
                <4>1 processState' = [processState EXCEPT ![p] = "critical"] BY <3>a DEF ProcessEnterCritical
                
                <4>2 processState'[p] = "critical" BY <1>1, <3>a DEF TypeOK, ProcessEnterCritical
                <4>3 processState'[p] = "waiting" BY <3>1
                <4>. QED BY <4>2, <4>3
            
            <3>b CASE p = 1 /\ q = 0
                <4>1 processState' = [processState EXCEPT ![q] = "critical"] BY <3>b DEF ProcessEnterCritical
                <4>2 processState[p] = "waiting" BY <1>1, <3>1, <4>1 DEF TypeOK
                <4>3 flag[p] = TRUE BY <4>2 DEF Inv, I, waitReqs
                <4>4 flag'[p] = TRUE BY <4>3 DEF ProcessEnterCritical
                <4>. QED BY <4>4
            
            <3>. QED BY <3>2, <3>a, <3>b
       
        <2>. QED BY <2>1, <2>a, <2>b, <2>c  DEF Inv, I            
                      
    
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
        <2>1 SUFFICES ASSUME NEW p \in {0, 1}, NEW q \in {0, 1}
                      PROVE (critReqs(p, q) /\ requestReqs(p, q) /\ waitReqs(p, q))'
                      BY DEF I
                       
        \* This is not a green to celebrate. This green mocks me.
        \* Well, actually. I suppose this green proves that the antecedent is always false, so the implication is vacuously true.
        \* Intuitively, this sort of makes sense because the whole point of PExC is that pS'[p] = idle.       
        <2>a critReqs(p, q)'  
            <3>1 SUFFICES ASSUME processState'[p] = "critical", p#q
                          PROVE FALSE \* (flag[q] = FALSE \/ turn = p \/ processState[q] = "sentRequest")' /\ flag'[p] = TRUE
                          BY DEF critReqs
                          
            <3>2 (p = 0 /\ q = 1) \/ (p = 1 /\ q = 0) BY <1>1, <3>1 DEF TypeOK
            
            <3>a CASE p = 0 /\ q = 1
                <4>1 processState' = [processState EXCEPT ![p] = "idle"] BY <3>a DEF ProcessExitCritical
                
                <4>2 processState'[p] = "idle" BY <1>1, <3>a DEF TypeOK, ProcessExitCritical
                <4>3 processState'[p] = "critical" BY <3>1
                <4>. QED BY <4>2, <4>3
            
            <3>b CASE p = 1 /\ q = 0
                <4>1 processState[0] = "critical" BY DEF ProcessExitCritical
                <4>2 processState' = [processState EXCEPT ![0] = "idle"] BY <3>a DEF ProcessExitCritical
                <4>3 processState'[0] = "idle" BY <1>1, <3>a DEF TypeOK, ProcessExitCritical
                
                <4>4 processState'[1] = "critical" BY <3>1, <3>b
                <4>5 processState[1] = "critical" BY <4>4 DEF ProcessExitCritical
                     
                <4>. QED BY <4>1, <4>5 DEF Inv, MutualExclusion
            
            <3>. QED BY <3>2, <3>a, <3>b
        
        <2>b requestReqs(p, q)'
            <3>1 SUFFICES ASSUME processState'[p] = "sentRequest", p#q
                          PROVE flag'[p] = TRUE
                          BY DEF requestReqs
            <3>2 (p = 0 /\ q = 1) \/ (p = 1 /\ q = 0) BY <1>1, <3>1 DEF TypeOK
            
            <3>a CASE p = 0 /\ q = 1
                <4>1 processState' = [processState EXCEPT ![p] = "idle"] BY <3>a DEF ProcessExitCritical
                
                <4>2 processState'[p] = "idle" BY <1>1, <3>a DEF TypeOK, ProcessExitCritical
                <4>3 processState'[p] = "sentRequest" BY <3>1
                <4>. QED BY <4>2, <4>3
            
            <3>b CASE p = 1 /\ q = 0
                <4>1 flag' = [flag EXCEPT ![0] = FALSE] BY DEF ProcessExitCritical
                <4>2 processState' = [processState EXCEPT ![0] = "idle"] BY DEF ProcessExitCritical
                <4>3 processState'[1] = "sentRequest" BY <3>1, <3>b
                <4>4 processState[1] = "sentRequest" BY <1>1, <4>2, <4>3 DEF TypeOK
                <4>5 flag[1] = TRUE BY <4>4 DEF Inv, I, requestReqs
                
                <4>6 flag' = [flag EXCEPT ![0] = FALSE] BY DEF ProcessExitCritical
                <4>7 flag'[1] = TRUE BY <1>1, <4>5, <4>6 DEF TypeOK
                                     
                <4>. QED BY <3>b, <4>7
            
            <3>. QED BY <3>2, <3>a, <3>b
        
        <2>c waitReqs(p, q)'
            <3>1 SUFFICES ASSUME processState'[p] = "waiting", p#q
                          PROVE flag'[p] = TRUE
                          BY DEF waitReqs
            <3>2 (p = 0 /\ q = 1) \/ (p = 1 /\ q = 0) BY <1>1, <3>1 DEF TypeOK
            
            <3>a CASE p = 0 /\ q = 1
                <4>1 processState' = [processState EXCEPT ![p] = "idle"] BY <3>a DEF ProcessExitCritical
                
                <4>2 processState'[p] = "idle" BY <1>1, <3>a DEF TypeOK, ProcessExitCritical
                <4>3 processState'[p] = "waiting" BY <3>1
                <4>. QED BY <4>2, <4>3
            
            <3>b CASE p = 1 /\ q = 0
                <4>1 flag' = [flag EXCEPT ![0] = FALSE] BY DEF ProcessExitCritical
                <4>2 processState' = [processState EXCEPT ![0] = "idle"] BY DEF ProcessExitCritical
                <4>3 processState'[1] = "waiting" BY <3>1, <3>b
                <4>4 processState[1] = "waiting" BY <1>1, <4>2, <4>3 DEF TypeOK
                <4>5 flag[1] = TRUE BY <4>4 DEF Inv, I, waitReqs
                
                <4>6 flag' = [flag EXCEPT ![0] = FALSE] BY DEF ProcessExitCritical
                <4>7 flag'[1] = TRUE BY <1>1, <4>5, <4>6 DEF TypeOK
                                     
                <4>. QED BY <3>b, <4>7
            
            <3>. QED BY <3>2, <3>a, <3>b

        <2>. QED BY <2>1, <2>a, <2>b, <2>c DEF Inv, I
        
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
\* Last modified Mon Jun 02 10:43:19 EDT 2025 by johnnguyen
\* Created Fri May 30 09:25:52 EDT 2025 by johnnguyen
