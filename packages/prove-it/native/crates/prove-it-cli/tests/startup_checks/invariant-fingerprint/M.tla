---- MODULE M ----
EXTENDS Naturals
CONSTANT M
VARIABLE x
Init == x = 0
Next == x < 3 /\ x' = x + 1
Inv == ~("a" \in ({M} \cup (1..20)))
====