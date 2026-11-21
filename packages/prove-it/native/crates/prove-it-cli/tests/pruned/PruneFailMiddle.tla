---- MODULE PruneFailMiddle ----
EXTENDS Naturals
CONSTANT S
VARIABLE x
Init == x = [s \in S |-> 0]
Grow(i) ==
    /\ x' \in [S -> 0..4]
    /\ x[i] < x'[i]
    /\ 12 \div (x'[i] - 2) # 5
    /\ \A j \in S \ {i} : x'[j] = x[j]
Next == \E i \in S : Grow(i)
Inv == TRUE
====
