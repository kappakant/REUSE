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
    
\* GCD Axioms for hiearchical proofs
AXIOM GCDProperty1 == \A p \in Number : GCD(p, p) = p
AXIOM GCDProperty2 == \A p, q \in Number : GCD(p, q) = GCD(q, p)
AXIOM GCDProperty3 == \A p, q \in Number : (p < q) => GCD(p, q) = GCD(p, q-p)

THEOREM NextProperty == InductiveInvariant /\ Next => InductiveInvariant'
<1> SUFFICES ASSUME InductiveInvariant, Next
             PROVE  InductiveInvariant'
<1> USE DEF InductiveInvariant, Next
<1>1 (x < y) \/ (y < x)
<1>a CASE x < y
<1>b CASE y < x
<1>2 QED
    BY <1>1, <1>a, <1>b
=============================================================================
\* Modification History
\* Last modified Thu May 29 08:56:02 EDT 2025 by johnnguyen
\* Created Thu May 29 08:48:04 EDT 2025 by johnnguyen
