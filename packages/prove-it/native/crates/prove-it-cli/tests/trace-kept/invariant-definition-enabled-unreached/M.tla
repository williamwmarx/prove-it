---- MODULE M ----
EXTENDS Naturals, Integers, TLC, FiniteSets, Sequences
VARIABLE x
Init == x = 0
Next == x' = x + 1
D == IF FALSE THEN ENABLED (x' = 1) ELSE <<{n \in Nat : n > 5}, {3, 1, 2}>>

Inv == x < 2 \/ "x" \in D[2]
====
