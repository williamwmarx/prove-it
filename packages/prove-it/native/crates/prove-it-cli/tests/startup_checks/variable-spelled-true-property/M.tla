---- MODULE M ----
EXTENDS Integers, TLC
Prop == \E x \in {1, 2} : x = 2
VARIABLE x
Init == x = 0
Next == x < 2 /\ x' = x + 1
====
