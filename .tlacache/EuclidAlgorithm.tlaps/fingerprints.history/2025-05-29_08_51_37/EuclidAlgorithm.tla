-------------------------- MODULE EuclidAlgorithm --------------------------
EXTENDS Integers

p | q == \E d \in 1..q : q = p * d
Divisors(q) == {d \in 1..q : d | q}
Maximum(S) == CHOOSE x \in S : \A y \in S : x >= y
GCD(p,q) == Maximum(Divisors(p) \cap Divisors(q))
Number == Nat \ {0}

CONSTANTS M, N
VARIABLES x, y

Init == (x = M) /\ (y = N)

Next == \/ /\ x < y
           /\ y' = y - x
           /\ x' = x
        \/ /\ y < x
           /\ x' = x-y
           /\ y' = y

Spec == Init /\ [][Next]_<<x,y>>

ResultCorrect == (x = y) => x = GCD(M, N)

THEOREM Correctness == Spec => []ResultCorrect

\* this holds because we have an easily seen inductive invariant:
InductiveInvariant == /\ x \in Number
                      /\ y \in Number
                      /\ GCD(x, y) = GCD(M, N)

\* Now we work on creating the proof as follows:

ASSUME NumberAssumption == M \in Number /\ N \in Number

THEOREM InitProperty == Init => InductiveInvariant
    BY NumberAssumption DEF Init, InductiveInvariant
=============================================================================
\* Modification History
\* Last modified Thu May 29 08:51:31 EDT 2025 by johnnguyen
\* Created Thu May 29 08:48:04 EDT 2025 by johnnguyen
