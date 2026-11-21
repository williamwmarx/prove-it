---- MODULE M ----
EXTENDS Integers, TLC
D == {x \in 1..3 : PrintT(x)}
VARIABLE x
Inv == 2 \in D
Init == x = 0
Next == x < 2 /\ x' = x + 1
====
