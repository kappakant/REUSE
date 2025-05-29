--------------------------- MODULE SimpleProgram ---------------------------

EXTENDS Integers
VARIABLES i, pc   

Init == (pc = "start") /\ (i = 0)

Pick == /\ pc = "start"  
        /\ i' \in 0..1000
        /\ pc' = "middle"

Add1 == /\ pc = "middle" 
        /\ i' = i + 1
        /\ pc' = "done"  
           
Next == Pick \/ Add1


=============================================================================
\* Modification History
\* Last modified Thu May 08 17:20:25 EDT 2025 by johnnguyen
\* Created Thu May 08 17:19:25 EDT 2025 by johnnguyen

