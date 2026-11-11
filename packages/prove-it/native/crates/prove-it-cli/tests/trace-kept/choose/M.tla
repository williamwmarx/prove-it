---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x = 0
P(F) == /\ x' \in {1, 2} /\ (CHOOSE g \in {F} : TRUE)[0] = x'
Next == P([i \in Nat |-> x'])
Inv == x # 2
====
