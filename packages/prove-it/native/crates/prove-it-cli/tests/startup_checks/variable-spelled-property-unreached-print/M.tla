---- MODULE M ----
EXTENDS Integers, TLC
Prop == \A x \in {1} : x = 1 \/ PrintT(x)
VARIABLE x
Init == x = 0
Next == x < 2 /\ x' = x + 1
====
