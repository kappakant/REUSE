--------------------------- MODULE IanFamousSpec ---------------------------
EXTENDS Integers, TLAPS

VARIABLES x

Init == x = 0

Next == x' = x + 2 \/ x' = x + 6

Safety == x /= 555

\* Intuitively, even numbers cannot be 555 and x will invariably be an even number

isEven(y) == y % 2 = 0

Inv == isEven(x) /\ x \in Nat
\* /land x \in Nat necessary for proving InductProperty

\* (1). Init => Inv
\* (2). Inv /\ Next => Inv'
\* (3). Inv => Safety

Spec == Init /\ [][Next]_x

THEOREM InitProperty == Init => Inv
    BY DEF Init, Inv, isEven
    \* Note, explicit definition of isEven is required
    
THEOREM InductProperty == (Inv /\ [Next]_x) => Inv'
    BY DEF Inv, Next, isEven

THEOREM SafetyProperty == Inv => Safety
    BY DEF Inv, isEven, Safety

THEOREM SpecImpliesSafety == Spec => []Safety
BY InitProperty, InductProperty, SafetyProperty, PTL DEF Spec
=============================================================================
\* Modification History
\* Last modified Thu May 29 10:13:37 EDT 2025 by johnnguyen
\* Created Wed May 28 00:35:37 EDT 2025 by johnnguyen
