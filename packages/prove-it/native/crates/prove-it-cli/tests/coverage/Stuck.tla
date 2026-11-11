---- MODULE Stuck ----
EXTENDS Naturals
VARIABLE x
Init == x \in {0, 1}
Next == x < 3 /\ x' = x + 1
====
