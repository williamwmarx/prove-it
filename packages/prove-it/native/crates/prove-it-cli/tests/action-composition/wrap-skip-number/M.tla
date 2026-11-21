---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
Init == x = 0
Next == FALSE /\ ((1) \cdot (x' = x))
====
