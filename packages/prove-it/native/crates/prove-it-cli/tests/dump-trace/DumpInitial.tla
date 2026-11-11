---- MODULE DumpInitial ----
EXTENDS Naturals, Sequences
VARIABLE x
Init == x \in {1, 2}
Next == x' = x
Inv == x > 5
====
