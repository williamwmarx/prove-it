---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x = [<<a, b>> \in {[k \in 1..2 |-> k]} |-> a]
Next == x' = x
====
