---- MODULE M ----
VARIABLE s
RECURSIVE A
A == {x \in {1,2} : 1 \in A}
Init == s = TRUE /\ 1 \in A
Next == UNCHANGED s
====
