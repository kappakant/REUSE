------------------------------- MODULE IndInv -------------------------------
EXTENDS ToyTwoCommit, TLAPS

THEOREM InitProperty == Init => Inv
    BY DEF Init, Inv, I, tmPreparedInv, RMsInv, TypeOK

\* Proved before strengthening InductiveInvariant (i.e. rmState[rm] = "commit" => tmPrepared = RMs only) 
\* Cleaned up the code a little, but likely some inefficient logic
THEOREM SafetyProperty == Inv => Consistent
    <1>1 SUFFICES ASSUME NEW rm1 \in RMs, NEW rm2 \in RMs, Inv
                  PROVE ~rmState[rm1] = "abort" \/ ~rmState[rm2] = "commit"
                  BY DEF Inv, Consistent
    <1>2 tmState = "init" \/ tmState = "abort" \/ tmState = "commit" BY <1>1 DEF Inv, TypeOK
    <1>3 SUFFICES ASSUME NEW tm2 \in RMs, NEW tm3 \in RMs, rmState[tm2] = "commit"
                  PROVE /\ tmState = "init" => rmState[tm3] # "abort"
                        /\ tmState = "abort" => FALSE
                        /\ tmState = "commit" => rmState[tm3] # "abort"
                  BY <1>2 DEF Consistent
                        
    <1>a tmState = "init" => rmState[tm3] # "abort"
        <2>1 SUFFICES ASSUME tmState = "init" PROVE rmState[tm3] # "abort" OBVIOUS
        <2>2 \A tm \in tmPrepared: rmState[tm] = "prepared" \/ rmState[tm] = "commit" BY <1>1, <2>1 DEF Inv, I, tmPreparedInv
        <2>3 tmPrepared = RMs BY <1>1, <1>3, <2>2 DEF Inv, I, RMsInv
        <2>4 rmState[tm3] = "prepared" \/ rmState[tm3] = "commit" BY <2>2, <2>3
        <2>5 rmState[tm3] # "abort" BY <2>4
        <2>. QED BY <2>4
    
    <1>b tmState = "abort" => FALSE
        <2>1 SUFFICES ASSUME tmState = "abort" PROVE FALSE OBVIOUS
        <2>2 \A tm \in tmPrepared: rmState[tm] = "prepared" \/ rmState[tm] = "abort" BY <1>1, <2>1 DEF Inv, I, tmPreparedInv
        <2>3 tmPrepared = RMs BY <1>1, <1>3 DEF Inv, I, RMsInv
        <2>4 rmState[tm2] = "prepared" \/ rmState[tm2] = "abort" BY <2>2, <2>3
        <2>5 rmState[tm2] = "commit" /\ (rmState[tm2] = "prepared" \/ rmState[tm2] = "abort") BY <1>3, <2>4
        <2>. QED BY <2>5
    
    <1>c tmState = "commit" => rmState[tm3] # "abort"
        <2>1 SUFFICES ASSUME tmState = "commit" PROVE rmState[tm3] # "abort" OBVIOUS
        <2>2 \A tm \in tmPrepared: rmState[tm] = "prepared" \/ rmState[tm] = "commit" BY <1>1, <2>1 DEF Inv, I, tmPreparedInv
        <2>3 tmPrepared = RMs BY <1>1, <1>3 DEF Inv, I, RMsInv
        <2>4 rmState[tm3] = "prepared" \/ rmState[tm3] = "commit" BY <2>1, <2>3
        <2>. QED BY <2>4
    
    <1>. QED BY <1>2, <1>a, <1>b, <1>c
                  

\* Super ugly and repetitive proof. A lot of what I assumed to be special cases were actually redundant and have general solutions
THEOREM InductiveProperty == Inv /\ Next => Inv'
    <1>1 SUFFICES ASSUME Inv, NEW rm \in RMs,
                         Prepare(rm) \/ Commit(rm) \/ Abort(rm) \/ SilentAbort(rm)
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
            
            
            <3>a tmPreparedInv' \* Ah, didn't do tmPrepared' properly. Fix later
                <4> SUFFICES ASSUME NEW tm \in tmPrepared'
                             PROVE /\ tmState' = "init" => rmState'[tm] = "prepared" \/ rmState'[tm] = "commit"
                                   /\ tmState' = "abort" => rmState'[tm] = "prepared" \/ rmState'[tm] = "abort"
                                   /\ tmState' = "commit" => /\ rmState'[tm] = "prepared" \/ rmState'[tm] = "commit"
                                                             /\ tmPrepared' = RMs
                             BY DEF tmPreparedInv
                <4>1 tmState' # "abort" BY <3>5
                <4>2 tmState' # "commit" BY <3>5
                <4>4 tmState' = "abort" => rmState'[tm] = "prepared" \/ rmState'[tm] = "abort" BY <4>1
                <4>5 tmState' = "commit" => /\ rmState'[tm] = "prepared" \/ rmState'[tm] = "commit"  \* Interestingly, if the BY is here it interprets
                                            /\ tmPrepared' = RMs BY <4>2                             \* The conjunction differently.
                <4>6 tm \in tmPrepared \/ rmState'[tm] = "prepared" BY <3>2, <3>3
                <4>7 tm \in tmPrepared => rmState[tm] = "prepared" \/ rmState[tm] = "commit" BY <1>1, <3>4 DEF Inv, I, tmPreparedInv
                <4>9 rmState[tm] = "prepared" \/ rmState[tm] = "commit" \/ rmState'[tm] = "prepared" BY <4>6, <4>7
                <4>10 rmState'[tm] = "prepared" \/ rmState'[tm] = "commit" \/ rmState'[tm] = "prepared" BY <1>1, <3>1, <4>9 DEF Inv, TypeOK
                <4>11 tmState' = "init" => rmState'[tm] = "prepared" \/ rmState'[tm] = "commit" BY <4>10
                <4>. QED BY <4>4, <4>5, <4>11 DEF tmPreparedInv
            
            
            <3>b RMsInv'
                <4> SUFFICES ASSUME NEW rm2 \in RMs, rmState'[rm2] = "commit" 
                             PROVE FALSE
                             BY DEF RMsInv
                <4>1 rmState[rm2] = "commit" BY <3>1
                <4>2 tmState = "commit" BY <1>1, <4>1 DEF Inv, I, RMsInv
                <4>. QED BY <3>4, <4>2
             
            <3>. QED BY <3>a, <3>b DEF I
        
        
        <2>b CASE Commit(rm)
            <3>1 rmState' = [rmState EXCEPT ![rm] = "commit"] BY <2>b DEF Commit
            <3>2 rmState'[rm] = "commit" BY <1>1, <1>a, <3>1 DEF TypeOK 
            <3>3 tmPrepared' = tmPrepared BY <2>b DEF Commit
            <3>4 tmPrepared = RMs BY <2>b DEF Commit
            <3>5 tmState = "init" \/ tmState = "commit" BY <2>b DEF Commit
            <3>6 tmState' = "commit" BY <2>b DEF Commit
                  
            <3>7 RMsInv' BY <3>3, <3>4, <3>6 DEF RMsInv    
            
            \* actually, both cases are true for basically the same reason. Much clean up to do in this section
            <3>a CASE tmState = "init"
                <4>1 tmPreparedInv' \* same as before
                    <5> SUFFICES ASSUME NEW tm \in tmPrepared'
                             PROVE /\ tmState' = "init" => rmState'[tm] = "prepared" \/ rmState'[tm] = "commit"
                                   /\ tmState' = "abort" => rmState'[tm] = "prepared" \/ rmState'[tm] = "abort"
                                   /\ tmState' = "commit" => /\ rmState'[tm] = "prepared" \/ rmState'[tm] = "commit"
                                                             /\ tmPrepared' = RMs
                             BY DEF tmPreparedInv
                    <5>1 tmState' # "init" BY <3>6
                    <5>2 tmState' # "abort" BY <3>6
                    <5>3 tmState' = "init" => rmState'[tm] = "prepared" \/ rmState'[tm] = "commit" BY <5>1
                    <5>4 tmState' = "abort" => rmState'[tm] = "prepared" \/ rmState'[tm] = "abort" BY <5>2
                    <5>5 rmState[tm] = "prepared" \/ rmState[tm] = "commit" BY <1>1, <3>3, <3>a DEF Inv, I, tmPreparedInv
                    <5>6 rmState'[tm] = "prepared" \/ rmState'[tm] = "commit" BY <1>1, <1>a, <3>1, <5>5 DEF TypeOK
                    <5>7 tmPrepared' = RMs BY <3>3, <3>4
                    <5>8 tmState' = "commit" => /\ rmState'[tm] = "prepared" \/ rmState'[tm] = "commit"
                                                /\ tmPrepared' = RMs BY <5>6, <5>7
                    <5>. QED BY <5>3, <5>4, <5>8
            

                <4>. QED BY <4>1, <3>7 DEF I
                
            <3>b CASE tmState = "commit"
                <4>1 tmPreparedInv'
                    <5> SUFFICES ASSUME NEW tm \in tmPrepared'
                             PROVE /\ tmState' = "init" => rmState'[tm] = "prepared" \/ rmState'[tm] = "commit"
                                   /\ tmState' = "abort" => rmState'[tm] = "prepared" \/ rmState'[tm] = "abort"
                                   /\ tmState' = "commit" => /\ rmState'[tm] = "prepared" \/ rmState'[tm] = "commit"
                                                             /\ tmPrepared' = RMs
                             BY DEF tmPreparedInv
                    <5>1 tmState' # "init" BY <3>6
                    <5>2 tmState' # "abort" BY <3>6
                    <5>3 tmState' = "init" => rmState'[tm] = "prepared" \/ rmState'[tm] = "commit" BY <5>1
                    <5>4 tmState' = "abort" => rmState'[tm] = "prepared" \/ rmState'[tm] = "abort" BY <5>2
                    <5>5 rmState[tm] = "prepared" \/ rmState[tm] = "commit" BY <1>1, <3>3, <3>b DEF Inv, I, tmPreparedInv
                    <5>6 rmState'[tm] = "prepared" \/ rmState'[tm] = "commit" BY <1>1, <1>a, <3>1, <5>5 DEF TypeOK
                    <5>7 tmPrepared' = RMs BY <3>3, <3>4
                    <5>8 tmState' = "commit" => /\ rmState'[tm] = "prepared" \/ rmState'[tm] = "commit"
                                                /\ tmPrepared' = RMs BY <5>6, <5>7
                    <5>. QED BY <5>3, <5>4, <5>8

                <4>. QED BY <4>1, <3>7 DEF I
                
            <3>. QED BY <3>5, <3>a, <3>b DEF I
            
        
        
        <2>c CASE Abort(rm)
            <3>1 rmState' = [rmState EXCEPT ![rm] = "abort"] BY <2>c DEF Abort
            <3>2 rmState'[rm] = "abort" BY <1>1, <1>a, <3>1 DEF TypeOK 
            <3>3 tmPrepared' = tmPrepared BY <2>c DEF Abort
            <3>4 tmState = "init" \/ tmState = "abort" BY <2>c DEF Abort
            <3>5 tmState' = "abort" BY <2>c DEF Abort
            
            <3>6 RMsInv'
                <4>1 SUFFICES ASSUME NEW rm2 \in RMs, rmState'[rm2] = "commit"
                                  PROVE FALSE
                                  BY DEF RMsInv
                <4>2 rmState[rm2] = "commit" BY <1>1, <3>1, <3>2, <4>1 DEF Inv, TypeOK
                <4>3 tmState = "commit" BY <1>1, <4>2 DEF Inv, I, RMsInv
                <4>. QED BY <3>4, <4>3
            
            <3>a CASE tmState = "init"
                <4>1 tmPreparedInv'
                    <5> SUFFICES ASSUME NEW tm \in tmPrepared'
                             PROVE /\ tmState' = "init" => rmState'[tm] = "prepared" \/ rmState'[tm] = "commit"
                                   /\ tmState' = "abort" => rmState'[tm] = "prepared" \/ rmState'[tm] = "abort"
                                   /\ tmState' = "commit" => /\ rmState'[tm] = "prepared" \/ rmState'[tm] = "commit"
                                                             /\ tmPrepared' = RMs
                             BY DEF tmPreparedInv
                    <5>1 tmState' # "init" BY <3>5
                    <5>2 tmState' # "commit" BY <3>5
                    <5>3 tmState' = "init" => rmState'[tm] = "prepared" \/ rmState'[tm] = "commit" BY <5>1
                    <5>4 tmState' = "commit" => /\ rmState'[tm] = "prepared" \/ rmState'[tm] = "commit" 
                                                /\ tmPrepared' = RMs BY <5>2
                                                
                    <5>5 rmState[tm] = "prepared" \/ rmState[tm] = "commit" BY <1>1, <3>3, <3>a DEF Inv, I, tmPreparedInv
                    <5>6 rmState'[tm] = "prepared" \/ rmState'[tm] = "commit" \/ rmState'[tm] = "abort" BY <1>1, <3>1, <5>5 DEF Inv, TypeOK
                    <5>7 CASE rmState'[tm] = "commit"
                        <6>1 rmState[tm] = "commit" BY <1>1, <3>1, <3>2, <5>7 DEF Inv, TypeOK
                        <6>2 tmState = "commit" BY <1>1, <3>3, <6>1 DEF Inv, I, RMsInv, TypeOK
                        <6>. QED BY <3>4, <6>2
                    <5>8 tmState' = "abort" => rmState'[tm] = "prepared" \/ rmState'[tm] = "abort" BY <5>6, <5>7
                  
                    <5>. QED BY <5>3, <5>4, <5>8 DEF tmPreparedInv

                <4>. QED BY <4>1, <3>6 DEF I
            
            
            <3>b CASE tmState = "abort"
                <4>1 tmPreparedInv'
                    <5> SUFFICES ASSUME NEW tm \in tmPrepared'
                             PROVE /\ tmState' = "init" => rmState'[tm] = "prepared" \/ rmState'[tm] = "commit"
                                   /\ tmState' = "abort" => rmState'[tm] = "prepared" \/ rmState'[tm] = "abort"
                                   /\ tmState' = "commit" => /\ rmState'[tm] = "prepared" \/ rmState'[tm] = "commit"
                                                             /\ tmPrepared' = RMs
                             BY DEF tmPreparedInv
                    <5>1 tmState' # "init" BY <3>5
                    <5>2 tmState' # "commit" BY <3>5
                    <5>3 tmState' = "init" => rmState'[tm] = "prepared" \/ rmState'[tm] = "commit" BY <5>1
                    <5>4 tmState' = "commit" => /\ rmState'[tm] = "prepared" \/ rmState'[tm] = "commit" 
                                                /\ tmPrepared' = RMs BY <5>2
                    <5>5 rmState[tm] = "prepared" \/ rmState[tm] = "abort" BY <1>1, <3>3, <3>b DEF Inv, I, tmPreparedInv
                    <5>6 rmState'[tm] = "prepared" \/ rmState'[tm] = "abort" BY <1>1, <3>1, <5>5 DEF Inv, TypeOK
                    <5>7 tmState' = "abort" => rmState'[tm] = "prepared" \/ rmState'[tm] = "abort" BY <5>6
                    <5>. QED BY <5>3, <5>4, <5>7 DEF tmPreparedInv
                    
                <4>. QED BY <4>1, <3>6 DEF I
            
            <3>. QED BY <3>4, <3>a, <3>b
        
        
        
        <2>d CASE SilentAbort(rm)
            <3>1 rmState' = [rmState EXCEPT ![rm] = "abort"] BY <2>d DEF SilentAbort
            <3>2 rmState'[rm] = "abort" BY <1>1, <1>a, <3>1 DEF TypeOK 
            <3>3 tmPrepared' = tmPrepared BY <2>d DEF SilentAbort
            <3>4 tmState' = tmState BY <2>d DEF SilentAbort
            <3>5 rmState[rm] = "working" BY <2>d DEF SilentAbort
            
            \* cases for every tmState?
            <3>6 tmState = "init" \/ tmState = "abort" \/ tmState = "commit" BY <1>1 DEF Inv, TypeOK
            
            <3>a CASE tmState = "init"
                <4>1 tmPreparedInv'
                    <5> SUFFICES ASSUME NEW tm \in tmPrepared'
                             PROVE /\ tmState' = "init" => rmState'[tm] = "prepared" \/ rmState'[tm] = "commit"
                                   /\ tmState' = "abort" => rmState'[tm] = "prepared" \/ rmState'[tm] = "abort"
                                   /\ tmState' = "commit" => /\ rmState'[tm] = "prepared" \/ rmState'[tm] = "commit"
                                                             /\ tmPrepared' = RMs
                             BY DEF tmPreparedInv
                    <5>1 tmState' # "abort" BY <3>4, <3>a
                    <5>2 tmState' # "commit" BY <3>4, <3>a
                    <5>3 tmState' = "abort" => rmState'[tm] = "prepared" \/ rmState'[tm] = "abort" BY <5>1
                    <5>4 tmState' = "commit" => /\ rmState'[tm] = "prepared" \/ rmState'[tm] = "commit" 
                                                /\ tmPrepared' = RMs BY <5>2
                    <5>5 rmState[tm] = "prepared" \/ rmState[tm] = "commit" BY <1>1, <3>3, <3>a DEF Inv, I, tmPreparedInv
                    <5>6 rmState'[tm] = "prepared" \/ rmState'[tm] = "commit" BY <3>1, <3>5, <5>5
                    <5>7 tmState' = "init" => rmState'[tm] = "prepared" \/ rmState'[tm] = "commit" BY <5>6
                       
                    <5>. QED BY <5>3, <5>4, <5>7
                
                <4>2 RMsInv'
                    <5>1 SUFFICES ASSUME NEW rm2 \in RMs, rmState'[rm2] = "commit"
                                  PROVE FALSE 
                                  BY DEF RMsInv
                    <5>2 rm2 # rm BY <5>1, <3>2
                    <5>3 rmState[rm2] = "commit" BY <1>1, <3>1, <5>1, <5>2 DEF Inv, TypeOK
                    <5>4 tmState = "commit" BY <1>1, <5>3 DEF Inv, I, RMsInv
                    <5>. QED BY <3>a, <5>4
            
                <4>. QED BY <4>1, <4>2 DEF I
            <3>b CASE tmState = "abort"
                <4>1 tmPreparedInv'
                    <5> SUFFICES ASSUME NEW tm \in tmPrepared'
                             PROVE /\ tmState' = "init" => rmState'[tm] = "prepared" \/ rmState'[tm] = "commit"
                                   /\ tmState' = "abort" => rmState'[tm] = "prepared" \/ rmState'[tm] = "abort"
                                   /\ tmState' = "commit" => /\ rmState'[tm] = "prepared" \/ rmState'[tm] = "commit"
                                                             /\ tmPrepared' = RMs
                             BY DEF tmPreparedInv
                    <5>1 tmState' # "init" BY <3>4, <3>b
                    <5>2 tmState' # "commit" BY <3>4, <3>b
                    <5>3 tmState' = "init" => rmState'[tm] = "prepared" \/ rmState'[tm] = "commit" BY <5>1
                    <5>4 tmState' = "commit" => /\ rmState'[tm] = "prepared" \/ rmState'[tm] = "commit" 
                                                /\ tmPrepared' = RMs BY <5>2
                    
                    <5>5 rmState[tm] = "prepared" \/ rmState[tm] = "abort" BY <1>1, <3>3, <3>b DEF Inv, I, tmPreparedInv
                    <5>6 rmState'[tm] = "prepared" \/ rmState'[tm] = "abort" BY <3>1, <5>5
                    <5>7 tmState' = "abort" => rmState'[tm] = "prepared" \/ rmState'[tm] = "abort" BY <5>6
                       
                    <5>. QED BY <5>3, <5>4, <5>7
                
                <4>2 RMsInv'
                    <5>1 SUFFICES ASSUME NEW rm2 \in RMs, rmState'[rm2] = "commit"
                                  PROVE FALSE 
                                  BY DEF RMsInv
                    <5>2 rm2 # rm BY <5>1, <3>2
                    <5>3 rmState[rm2] = "commit" BY <1>1, <3>1, <5>1, <5>2 DEF Inv, TypeOK
                    <5>4 tmState = "commit" BY <1>1, <5>3 DEF Inv, I, RMsInv
                    <5>. QED BY <3>b, <5>4
                
                <4>. QED BY <4>1, <4>2 DEF I
            
            
            <3>c CASE tmState = "commit"
                <4>1 tmPreparedInv'
                    <5> SUFFICES ASSUME NEW tm \in tmPrepared'
                             PROVE /\ tmState' = "init" => rmState'[tm] = "prepared" \/ rmState'[tm] = "commit"
                                   /\ tmState' = "abort" => rmState'[tm] = "prepared" \/ rmState'[tm] = "abort"
                                   /\ tmState' = "commit" => /\ rmState'[tm] = "prepared" \/ rmState'[tm] = "commit"
                                                             /\ tmPrepared' = RMs
                             BY DEF tmPreparedInv
                    <5>1 tmState' # "init" BY <3>4, <3>c
                    <5>2 tmState' # "abort" BY <3>4, <3>c
                    <5>3 tmState' = "init" => rmState'[tm] = "prepared" \/ rmState'[tm] = "commit" BY <5>1
                    <5>4 tmState' = "abort" => rmState'[tm] = "prepared" \/ rmState'[tm] = "abort" BY <5>2
                    <5>5 /\ rmState[tm] = "prepared" \/ rmState[tm] = "commit"
                         /\ tmPrepared = RMs BY <1>1, <3>3, <3>c DEF Inv, I, tmPreparedInv
                    <5>6 tm # rm BY <3>5, <5>5
                    <5>7 rmState'[tm] = "prepared" \/ rmState'[tm] = "commit" BY <1>1, <3>1, <5>5, <5>6 DEF Inv, TypeOK
                    <5>8 tmState' = "commit" => /\ rmState'[tm] = "prepared" \/ rmState'[tm] = "commit" 
                                                /\ tmPrepared' = RMs BY <3>3, <5>5, <5>7 
                    <5>. QED BY <3>3, <5>3, <5>4, <5>8
                    
                <4>2 RMsInv'
                    <5>1 SUFFICES ASSUME NEW rm2 \in RMs, rmState'[rm2] = "commit"
                                  PROVE tmPrepared' = RMs /\ tmState' = "commit"
                                  BY DEF RMsInv 
                    <5>2 rm2 # rm BY <3>2, <5>1
                    <5>3 rmState[rm2] = "commit" BY <1>1, <3>1, <5>1, <5>2 DEF Inv, TypeOK
                    <5>4 tmPrepared = RMs BY <1>1, <5>3 DEF Inv, I, RMsInv
                    <5>5 tmPrepared' = RMs BY <3>3, <5>4
                    <5>. QED BY <3>4, <3>c, <5>5
                    
                <4>. QED BY <4>1, <4>2 DEF I
            
            <3>. QED BY <3>6, <3>a, <3>b, <3>c
        
        
        <2>. QED BY <2>1, <2>a, <2>b, <2>c, <2>d

    
    <1>. QED BY <1>a, <1>b
    
THEOREM StutterProof == Inv /\ vars' = vars => Inv'
    <1>1 SUFFICES ASSUME Inv, vars' = vars
                  PROVE Inv'
                  OBVIOUS
    <1>2 Inv' BY <1>1 DEF Inv, I, tmPreparedInv, RMsInv, TypeOK, vars
    <1>. QED BY <1>2  

THEOREM InductiveAndStutterProof == 
    Inv /\ [Next]_vars => Inv'
    BY InductiveProperty, StutterProof

THEOREM InductiveInvariant == 
    /\ Init => Inv
    /\ Inv /\ [Next]_vars => Inv'
    /\ Inv => Consistent
    BY InitProperty, InductiveAndStutterProof, SafetyProperty

THEOREM AlwaysConsistent ==
    TestSpec => []Consistent
    BY InductiveInvariant, PTL DEF TestSpec


=============================================================================
\* Modification History
\* Last modified Wed Jun 04 16:33:26 EDT 2025 by johnnguyen
\* Created Mon Jun 02 13:14:02 EDT 2025 by johnnguyen
