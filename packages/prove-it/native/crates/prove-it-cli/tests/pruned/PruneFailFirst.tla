---- MODULE PruneFailFirst ----
EXTENDS Naturals
CONSTANT S
VARIABLE x
Init == x = [s \in S |-> 1]
Grow(i) ==
    /\ x' \in [S -> 0..3]
    /\ 6 \div x'[i] > 1
    /\ \A j \in S \ {i} : x'[j] = x[j]
Next == \E i \in S : Grow(i)
Inv == TRUE
====
