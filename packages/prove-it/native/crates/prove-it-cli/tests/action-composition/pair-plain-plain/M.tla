---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
Init == x = 0
Next == (x' = x) \cdot (x' = x)
====
