---- MODULE PruneFixedRead ----
EXTENDS Naturals
CONSTANT S
VARIABLE x
First == CHOOSE s \in S : TRUE
Init == x = [s \in S |-> 0]
Grow(i) ==
    /\ x' \in [S -> 0..2]
    /\ x'[First] <= 1 \/ x[First] = 1
    /\ x[i] < x'[i]
    /\ \A j \in S \ {i} : x'[j] = x[j]
Held(i) ==
    /\ x' \in [S -> 0..2]
    /\ \A j \in S \ {i} : x'[j] = x[j] + 5
Next == \E i \in S : Grow(i) \/ Held(i)
Inv == TRUE
====
