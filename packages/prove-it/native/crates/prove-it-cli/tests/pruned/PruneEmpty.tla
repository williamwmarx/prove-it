---- MODULE PruneEmpty ----
EXTENDS Naturals
CONSTANT S
VARIABLE x
Init == x = [s \in S |-> 0]
Grow(i) ==
    /\ x' \in [S -> 0..1]
    /\ x[i] < x'[i]
    /\ \A j \in S \ S : x'[j] = x[j]
Next == \E i \in S : Grow(i)
Inv == TRUE
====
