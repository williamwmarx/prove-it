---- MODULE PruneWalked ----
EXTENDS Naturals
CONSTANT S
VARIABLE x
Le(a, b) == a <= b /\ b - a <= 2
Init == x = [s \in S |-> 0]
Grow(i) ==
    /\ x' \in [S -> 0..3]
    /\ Le(x[i], x'[i])
    /\ \E k \in 1..2 : x'[i] >= k
    /\ x'[i] = 3 \/ x[i] < 2
    /\ \A j \in S \ {i} : x'[j] = x[j]
Next == \E i \in S : Grow(i)
Inv == \A s \in S : x[s] < 3
====
