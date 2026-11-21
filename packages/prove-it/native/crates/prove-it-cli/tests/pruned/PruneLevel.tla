---- MODULE PruneLevel ----
EXTENDS Naturals, TLC
CONSTANT S
VARIABLE x
Init == x = [s \in S |-> 0]
Grow(i) ==
    /\ x' \in [S -> 0..3]
    /\ x[i] < x'[i]
    /\ \A j \in S \ {i} : x'[j] = IF TLCGet("level") > 2 THEN x[j] ELSE 0
Next == \E i \in S : Grow(i)
Inv == ~(\A s \in S : x[s] >= 1)
====
