---- MODULE M ----
EXTENDS TLC, Naturals
VARIABLE x
Init == x = 0
Next == x' = x
A == Any
Inv == 1 \in A /\ TRUE \in A /\ {} \in A /\ {1, 2} \in SUBSET A /\ 1 \in (A \cap {1})
====
