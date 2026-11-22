---- MODULE PruneGrow ----
EXTENDS Naturals
CONSTANT S
VARIABLE x
Init == x = [s \in S |-> 0]
Grow(i) ==
    /\ \A j \in S : x[j] <= x[i]
    /\ x' \in [S -> 0..3]
    /\ x[i] <= x'[i]
    /\ x'[i] # x[i]
    /\ \A j \in S \ {i} : x'[j] = x[j]
Next == \E i \in S : Grow(i)
Inv == ~(\A s \in S : x[s] >= 2)
====
