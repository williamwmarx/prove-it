---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x \subseteq 1..2 /\ PrintT(x)
Next == x' \in {{2, 1}} /\ PrintT(x')
====
