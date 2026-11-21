---- MODULE M ----
EXTENDS Naturals, TLC
CONSTANT S, T
VARIABLE x
Init == x \in S
Next == x' = x
Sym == {[e \in {1, 2} |-> e], [e \in {1, 2} |-> 1]}
====
