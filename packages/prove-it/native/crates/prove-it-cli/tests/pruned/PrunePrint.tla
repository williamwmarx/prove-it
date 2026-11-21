---- MODULE PrunePrint ----
EXTENDS Naturals, TLC
CONSTANT S
VARIABLE x
Init == x = [s \in S |-> 0]
Grow(i) ==
    /\ x' \in [S -> 0..1]
    /\ PrintT(<<i, x'>>)
    /\ x[i] < x'[i]
    /\ \A j \in S \ {i} : x'[j] = x[j]
Next == \E i \in S : Grow(i)
Inv == TRUE
====
