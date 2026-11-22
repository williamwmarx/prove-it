---- MODULE PruneFailBody ----
EXTENDS Naturals
CONSTANT S
VARIABLE x
Init == x = [s \in S |-> 0]
Grow(i) ==
    /\ x' \in [S -> 0..2]
    /\ x[i] < x'[i]
    /\ \A j \in S \ {i} : x'[j] = 4 \div (1 - x[j])
Next == \E i \in S : Grow(i)
Inv == TRUE
====
