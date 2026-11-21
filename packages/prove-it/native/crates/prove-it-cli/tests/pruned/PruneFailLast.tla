---- MODULE PruneFailLast ----
EXTENDS Naturals
CONSTANT S
VARIABLE x
Init == x = [s \in S |-> 0]
Grow(i) ==
    /\ x' \in [S -> 0..3]
    /\ x[i] + 1 = x'[i] \/ x[i] = 2
    /\ 12 \div (3 - x'[i]) > 0
    /\ \A j \in S \ {i} : x'[j] = x[j]
Next == \E i \in S : Grow(i)
Inv == TRUE
====
