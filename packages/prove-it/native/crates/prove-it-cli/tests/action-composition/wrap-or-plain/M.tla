---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
Init == x = 0
Next == (FALSE /\ x' = x) \/ ((x' = x) \cdot (x' = x))
====
