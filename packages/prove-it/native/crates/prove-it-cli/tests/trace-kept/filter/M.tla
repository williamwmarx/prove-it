---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x = 0
P(S) == /\ x' \in {1, 2} /\ x' \in S /\ x' \in S
Next == P({v \in Nat : v = x'})
Inv == x # 2
====
