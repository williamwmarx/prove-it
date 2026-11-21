---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
Init == x = 0
Next == Assert(FALSE,"FIRST") /\ ((PrintT("OPERAND") /\ x' = x) \cdot (x' = x))
====
