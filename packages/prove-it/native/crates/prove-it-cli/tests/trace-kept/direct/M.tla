---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x = 0
P(v) == /\ x' \in {1, 2} /\ v = x' /\ v = x'
Next == P(x' + 0)
Inv == x # 2
====
