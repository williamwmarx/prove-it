---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x = 0
P(F(_)) == /\ x' \in {1, 2} /\ F(0) = x'
Next == P(LAMBDA i : x')
Inv == x # 2
====
