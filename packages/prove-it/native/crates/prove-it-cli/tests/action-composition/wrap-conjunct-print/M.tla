---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
Init == x = 0
Next == x = 0 /\ ((PrintT("OPERAND") /\ x' = x) \cdot (x' = x))
====
