---- MODULE M ----
EXTENDS Naturals, Integers, TLC, FiniteSets, Sequences
VARIABLE x
---- MODULE N ----
VARIABLE y
D == <<[i \in Nat |-> i + y], {3, 1, 2}>>
====
I == INSTANCE N WITH y <- x
Init == x = 0
Next == x' = x + 1
Inv == x < 2 \/ "x" \in I!D[2]

====
