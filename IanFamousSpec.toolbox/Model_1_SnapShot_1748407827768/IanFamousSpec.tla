--------------------------- MODULE IanFamousSpec ---------------------------
EXTENDS Integers

VARIABLES x

Init == x = 0

Next == (x' = x + 2) \/ (x' = x + 6)

Safety == x /= 555

\* Intuitively, even numbers cannot be 555 and x will invariably be an even number

isEven(y) == y % 2 = 0

Inv == isEven(x)

\* (1). Init => Inv
\* (2). Inv /\ Next => Inv'
\* (3). Inv => Safety

Spec == Init /\ [][Next]_x

THEOREM Correctness == Spec => []Inv

=============================================================================
\* Modification History
\* Last modified Wed May 28 00:49:23 EDT 2025 by johnnguyen
\* Created Wed May 28 00:35:37 EDT 2025 by johnnguyen
