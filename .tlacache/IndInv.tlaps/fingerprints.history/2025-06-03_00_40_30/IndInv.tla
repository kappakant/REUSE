------------------------------- MODULE IndInv -------------------------------
EXTENDS ToyTwoCommit, InvLemmas

THEOREM InitProperty == Init => Inv
    BY DEF Init, Inv, I, TypeOK

THEOREM SafetyProperty == Inv => Consistent
    <1>1 SUFFICES ASSUME NEW rm1 \in RMs, NEW rm2 \in RMs, Inv
                  PROVE ~rmState[rm1] = "abort" \/ ~rmState[rm2] = "commit"
                  BY DEF Inv, Consistent
    <1>2 tmState = "init" \/ tmState = "abort" \/ tmState = "commit" BY <1>1 DEF Inv, TypeOK
    
    <1>a CASE tmState = "init"
        <2>1 \A tm \in tmPrepared: rmState[tm] = "prepared" BY <1>1, <1>a DEF Inv, I
        <2>2 SUFFICES ASSUME NEW tm2 \in RMs, rmState[tm2] = "commit"
                      PROVE FALSE
                      BY DEF Consistent
        <2>4 tmPrepared = RMs BY <1>1, <2>2 DEF Inv, I 
        <2>5 rmState[tm2] = "prepared" BY <2>1, <2>2, <2>4
        <2>. QED BY <2>2, <2>5
    
    <1>b CASE tmState = "abort"
        <2>1 \A tm \in tmPrepared: rmState[tm] = "prepared" \/ rmState[tm] = "abort" BY <1>1, <1>b DEF Inv, I
        <2>2 SUFFICES ASSUME NEW tm2 \in RMs, rmState[tm2] = "commit"
                      PROVE FALSE
                      BY DEF Consistent
        <2>3 tmPrepared = RMs BY <1>1, <2>2 DEF Inv, I 
        <2>4 rmState[tm2] = "prepared" \/ rmState[tm2] = "abort" BY <2>1, <2>2, <2>3
        <2>. QED BY <2>2, <2>4
    
    <1>c CASE tmState = "commit"
        <2>1 \A tm \in tmPrepared: rmState[tm] = "prepared" \/ rmState[tm] = "commit" BY <1>1, <1>c DEF Inv, I
        <2>2 SUFFICES ASSUME NEW tm2 \in RMs, NEW tm3 \in RMs, rmState[tm2] = "commit"
                      PROVE rmState[tm3] # "abort"
                      BY DEF Consistent
        <2>3 tmPrepared = RMs BY <1>1, <2>2 DEF Inv, I 
        <2>4 rmState[tm3] = "prepared" \/ rmState[tm3] = "commit" BY <2>1, <2>2, <2>3
        <2>. QED BY <2>2, <2>4
    
    <1>. QED BY <1>2, <1>a, <1>b, <1>c
                  

THEOREM InductiveProperty == Inv /\ Next => Inv'
    <1>1 SUFFICES ASSUME Inv, Next
                  PROVE /\ TypeOK'
                        /\ I'
                  BY DEF Inv, I
    
    <1>a TypeOK'
        <2>1 /\ rmState \in [RMs -> {"working", "prepared", "commit", "abort"}]
             /\ tmState \in {"init", "commit", "abort"}
             /\ tmPrepared \in SUBSET RMs BY <1>1 DEF Inv, TypeOK
        <2>2 PICK rm \in RMs: Prepare(rm) \/ Commit(rm) \/ Abort(rm) \/ SilentAbort(rm) BY <1>1 DEF Next
        
        
        <2>a CASE Prepare(rm)
            <3>1 rmState' = [rmState EXCEPT ![rm] = "prepared"] BY <2>a DEF Prepare
            <3>2 rmState' \in [RMs -> {"working", "prepared", "commit", "abort"}] BY <2>1, <3>1
            
            <3>3 tmPrepared' = tmPrepared \cup {rm} BY <2>a DEF Prepare
            <3>4 tmPrepared' \in SUBSET RMs BY <2>1, <2>2, <3>3
            
            <3>5 UNCHANGED(tmState) BY <2>a DEF Prepare
            <3>6 tmState' \in {"init", "commit", "abort"} BY <2>1, <3>5
            <3>. QED BY <3>2, <3>4, <3>6 DEF TypeOK
            
            
        <2>b CASE Commit(rm)
            <3>1 rmState' = [rmState EXCEPT ![rm] = "commit"] BY <2>b DEF Commit
            <3>2 rmState' \in [RMs -> {"working", "prepared", "commit", "abort"}] BY <2>1, <3>1
            
            <3>3 tmPrepared' = RMs BY <2>b DEF Commit
            <3>4 tmPrepared' \in SUBSET RMs BY <2>1, <2>2, <3>3
            
            <3>5 tmState' = "commit" BY <2>b DEF Commit
            <3>. QED BY <3>2, <3>4, <3>5 DEF TypeOK
            

        <2>c CASE Abort(rm)
            <3>1 rmState' = [rmState EXCEPT ![rm] = "abort"] BY <2>c DEF Abort
            <3>2 rmState' \in [RMs -> {"working", "prepared", "commit", "abort"}] BY <2>1, <3>1
            
            <3>3 UNCHANGED(tmPrepared) BY <2>c DEF Abort
            <3>4 tmPrepared' \in SUBSET RMs BY <2>1, <2>2, <3>3
  
            <3>5 tmState' = "abort" BY <2>c DEF Abort       
            <3>. QED BY <3>2, <3>4, <3>5 DEF TypeOK
            
            
        <2>d CASE SilentAbort(rm)
            <3>1 rmState' = [rmState EXCEPT ![rm] = "abort"] BY <2>d DEF SilentAbort
            <3>2 rmState' \in [RMs -> {"working", "prepared", "commit", "abort"}] BY <2>1, <3>1
            
            <3>3 tmPrepared' = tmPrepared BY <2>d DEF SilentAbort
            <3>4 tmPrepared' \in SUBSET RMs BY <2>1, <2>2, <3>3
            
            <3>5 UNCHANGED(tmState) BY <2>d DEF SilentAbort
            <3>6 tmState' \in {"init", "commit", "abort"} BY <2>1, <3>5
            <3>. QED BY <3>2, <3>4, <3>6 DEF TypeOK
    
        <2>. QED BY <2>2, <2>a, <2>b, <2>c, <2>d
    
    <1>b I'
        <2>1 /\ \A rm \in tmPrepared:
                /\ tmState = "init"   => rmState[rm] = "prepared"
                /\ tmState = "abort"  => rmState[rm] = "prepared" \/ rmState[rm] = "abort"
                /\ tmState = "commit" => /\ rmState[rm] = "prepared" \/ rmState[rm] = "commit"
                                         /\ tmPrepared = RMs 
             /\ \A rm \in RMs:
                rmState[rm] = "commit" => tmPrepared = RMs BY <1>1 DEF Inv, I
                
        \* we'll use the ol' 1-2 punch. Assume arbitrary rm in RMs, prove second part.
        \* Then, assume arbitrary tm in tmPrepared. prove first part
        
        <2>2 RMsInv' /\ tmPreparedInv'
            <3>1 TAKE rm \in RMs
            <3>a RMsInv'
            <3>b tmPreparedInv'
            <3>. QED

        <2>. QED
    
    <1>. QED BY <1>a, <1>b





=============================================================================
\* Modification History
\* Last modified Tue Jun 03 00:40:28 EDT 2025 by johnnguyen
\* Created Mon Jun 02 13:14:02 EDT 2025 by johnnguyen
