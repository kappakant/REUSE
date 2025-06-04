------------------------------- MODULE IndInv -------------------------------
EXTENDS ToyTwoCommit

THEOREM InitProperty == Init => Inv
    BY DEF Init, Inv, I, tmPreparedInv, RMsInv, TypeOK

\* Lots of repetition, can shorten proof significantly by moving some lines up in the hierarchy
THEOREM SafetyProperty == Inv => Consistent
    <1>1 SUFFICES ASSUME NEW rm1 \in RMs, NEW rm2 \in RMs, Inv
                  PROVE ~rmState[rm1] = "abort" \/ ~rmState[rm2] = "commit"
                  BY DEF Inv, Consistent
    <1>2 tmState = "init" \/ tmState = "abort" \/ tmState = "commit" BY <1>1 DEF Inv, TypeOK
    
    <1>a CASE tmState = "init"
        <2>1 \A tm \in tmPrepared: rmState[tm] = "prepared" \/ rmState[tm] = "commit" BY <1>1, <1>a DEF Inv, I, tmPreparedInv
        <2>2 SUFFICES ASSUME NEW tm2 \in RMs, NEW tm3 \in RMs, rmState[tm2] = "commit"
                      PROVE rmState[tm3] # "abort"
                      BY DEF Consistent
        <2>3 tmPrepared = RMs BY <1>1, <2>2 DEF Inv, I, RMsInv
        <2>4 rmState[tm3] = "prepared" \/ rmState[tm3] = "commit" BY <2>1, <2>2, <2>3
        <2>. QED BY <2>2, <2>4
    
    <1>b CASE tmState = "abort"
        <2>1 \A tm \in tmPrepared: rmState[tm] = "prepared" \/ rmState[tm] = "abort" BY <1>1, <1>b DEF Inv, I, tmPreparedInv
        <2>2 SUFFICES ASSUME NEW tm2 \in RMs, rmState[tm2] = "commit"
                      PROVE FALSE
                      BY DEF Consistent
        <2>3 tmPrepared = RMs BY <1>1, <2>2 DEF Inv, I, RMsInv
        <2>4 rmState[tm2] = "prepared" \/ rmState[tm2] = "abort" BY <2>1, <2>2, <2>3
        <2>. QED BY <2>2, <2>4
    
    <1>c CASE tmState = "commit"
        <2>1 \A tm \in tmPrepared: rmState[tm] = "prepared" \/ rmState[tm] = "commit" BY <1>1, <1>c DEF Inv, I, tmPreparedInv
        <2>2 SUFFICES ASSUME NEW tm2 \in RMs, NEW tm3 \in RMs, rmState[tm2] = "commit"
                      PROVE rmState[tm3] # "abort"
                      BY DEF Consistent
        <2>3 tmPrepared = RMs BY <1>1, <2>2 DEF Inv, I, RMsInv
        <2>4 rmState[tm3] = "prepared" \/ rmState[tm3] = "commit" BY <2>1, <2>2, <2>3
        <2>. QED BY <2>2, <2>4
    
    <1>. QED BY <1>2, <1>a, <1>b, <1>c
                  

THEOREM InductiveProperty == Inv /\ Next => Inv'
    <1>1 SUFFICES ASSUME Inv, NEW rm \in RMs, \* Note, this rm is an existential instantiation
                         Prepare(rm) \/ Commit(rm) \/ Abort(rm) \/ SilentAbort(rm) \* Essentially just Next, perhaps inelegant.
                  PROVE /\ TypeOK'
                        /\ I'
                  BY DEF Inv, Next
                  
    <1>a TypeOK'
        <2>1 /\ rmState \in [RMs -> {"working", "prepared", "commit", "abort"}]
             /\ tmState \in {"init", "commit", "abort"}
             /\ tmPrepared \in SUBSET RMs BY <1>1 DEF Inv, TypeOK
        \* <2>2 PICK rm \in RMs: Prepare(rm) \/ Commit(rm) \/ Abort(rm) \/ SilentAbort(rm) BY <1>1 DEF Next
        
         
        <2>a CASE Prepare(rm)
            <3>1 rmState' = [rmState EXCEPT ![rm] = "prepared"] BY <2>a DEF Prepare
            <3>2 rmState' \in [RMs -> {"working", "prepared", "commit", "abort"}] BY <2>1, <3>1
            
            <3>3 tmPrepared' = tmPrepared \cup {rm} BY <2>a DEF Prepare
            <3>4 tmPrepared' \in SUBSET RMs BY <1>1, <2>1, <3>3
            
            <3>5 UNCHANGED(tmState) BY <2>a DEF Prepare
            <3>6 tmState' \in {"init", "commit", "abort"} BY <2>1, <3>5
            <3>. QED BY <3>2, <3>4, <3>6 DEF TypeOK
            
            
        <2>b CASE Commit(rm)
            <3>1 rmState' = [rmState EXCEPT ![rm] = "commit"] BY <2>b DEF Commit
            <3>2 rmState' \in [RMs -> {"working", "prepared", "commit", "abort"}] BY <2>1, <3>1
            
            <3>3 tmPrepared' = RMs BY <2>b DEF Commit
            <3>4 tmPrepared' \in SUBSET RMs BY <1>1, <2>1, <3>3
            
            <3>5 tmState' = "commit" BY <2>b DEF Commit
            <3>. QED BY <3>2, <3>4, <3>5 DEF TypeOK
            

        <2>c CASE Abort(rm)
            <3>1 rmState' = [rmState EXCEPT ![rm] = "abort"] BY <2>c DEF Abort
            <3>2 rmState' \in [RMs -> {"working", "prepared", "commit", "abort"}] BY <2>1, <3>1
            
            <3>3 UNCHANGED(tmPrepared) BY <2>c DEF Abort
            <3>4 tmPrepared' \in SUBSET RMs BY <1>1, <2>1, <3>3
  
            <3>5 tmState' = "abort" BY <2>c DEF Abort       
            <3>. QED BY <3>2, <3>4, <3>5 DEF TypeOK
            
            
        <2>d CASE SilentAbort(rm)
            <3>1 rmState' = [rmState EXCEPT ![rm] = "abort"] BY <2>d DEF SilentAbort
            <3>2 rmState' \in [RMs -> {"working", "prepared", "commit", "abort"}] BY <2>1, <3>1
            
            <3>3 tmPrepared' = tmPrepared BY <2>d DEF SilentAbort
            <3>4 tmPrepared' \in SUBSET RMs BY <1>1, <2>1, <3>3
            
            <3>5 UNCHANGED(tmState) BY <2>d DEF SilentAbort
            <3>6 tmState' \in {"init", "commit", "abort"} BY <2>1, <3>5
            <3>. QED BY <3>2, <3>4, <3>6 DEF TypeOK
    
        <2>. QED BY <1>1, <2>a, <2>b, <2>c, <2>d
    
    <1>b I'
        \* Cases for next
        <2>1 Prepare(rm) \/ Commit(rm) \/ Abort(rm) \/ SilentAbort(rm) BY <1>1
        
        <2>a CASE Prepare(rm)
            <3>1 rmState' = [rmState EXCEPT ![rm] = "prepared"] BY <2>a DEF Prepare
            <3>2 rmState'[rm] = "prepared" BY <1>1, <1>a, <3>1 DEF TypeOK
            <3>3 tmPrepared' = tmPrepared \cup {rm} BY <2>a DEF Prepare
            <3>4 tmState = "init" BY <2>a DEF Prepare
            <3>5 tmState' = "init" BY <2>a, <3>3 DEF Prepare
            <3>6 rm \in tmPrepared' BY <3>2
            
            
            <3>a tmPreparedInv' \* Should be correct, some quirk of instantiation, I suppose. 
                <4> SUFFICES ASSUME NEW tm \in tmPrepared
                             PROVE /\ tmState' = "init" => rmState'[tm] = "prepared" \/ rmState'[tm] = "commit"
                                   /\ tmState' = "abort" => rmState'[tm] = "prepared" \/ rmState'[tm] = "abort"
                                   /\ tmState' = "commit" => /\ rmState'[tm] = "prepared" /\ rmState'[tm] = "commit"
                                                             /\ tmPrepared' = RMs
                             BY DEF tmPreparedInv
                <4>1 tmState' # "abort" BY <3>5
                <4>2 tmState' # "commit" BY <3>5
                <4>4 tmState' = "abort" => rmState'[tm] = "prepared" \/ rmState'[tm] = "abort" BY <4>1
                <4>5 tmState' = "commit" => /\ rmState'[tm] = "prepared" /\ rmState'[tm] = "commit"  \* Interestingly, if the BY is here it interprets
                                            /\ tmPrepared' = RMs BY <4>2                             \* The conjunction differently.
                <4>6 rmState[tm] = "prepared" \/ rmState[tm] = "commit" BY <1>1, <3>4 DEF Inv, I, tmPreparedInv
                <4>7 rmState'[tm] = "prepared" \/ rmState'[tm] = "commit" BY <1>1, <3>1, <4>6 DEF Inv, TypeOK
                <4>8 tmState' = "init" => rmState'[tm] = "prepared" \/ rmState'[tm] = "commit" BY <4>7
                <4>. QED BY <3>6, <4>4, <4>5, <4>8 DEF tmPreparedInv
            
            
            <3>b RMsInv'
                <4> SUFFICES ASSUME NEW rm2 \in RMs, rmState'[rm2] = "commit" 
                             PROVE tmPrepared' = RMs
                             BY DEF RMsInv
                <4>1 rmState[rm2] = "commit" BY <3>1
                <4>2 tmPrepared = RMs BY <1>1, <4>1 DEF Inv, I, RMsInv
                <4>. QED BY <3>3, <4>2 DEF RMsInv
             
            <3>. QED BY <3>a, <3>b DEF I
        
        
        <2>b CASE Commit(rm)
            <3>1 rmState' = [rmState EXCEPT ![rm] = "commit"] BY <2>b DEF Commit
            <3>2 rmState'[rm] = "commit" BY <1>1, <1>a, <3>1 DEF TypeOK 
            <3>3 tmPrepared' = tmPrepared BY <2>b DEF Commit
            <3>4 tmState = "init" \/ tmState = "commit" BY <2>b DEF Commit
            <3>5 tmState' = "commit" BY <2>b DEF Commit
            
            <3>a CASE tmState = "init"
                <4>a tmPreparedInv'
            
            
                <4>b RMsInv'
                
                <4>. QED
                
            <3>b CASE tmState = "commit"
            
            <3>. QED BY <3>4, <3>a, <3>b DEF I
            
        
        
        <2>c CASE Abort(rm)
        
        
        <2>d CASE SilentAbort(rm)
        
        
        <2>. QED BY <2>1, <2>a, <2>b, <2>c, <2>d

    
    <1>. QED BY <1>a, <1>b





=============================================================================
\* Modification History
\* Last modified Wed Jun 04 09:01:53 EDT 2025 by johnnguyen
\* Created Mon Jun 02 13:14:02 EDT 2025 by johnnguyen
