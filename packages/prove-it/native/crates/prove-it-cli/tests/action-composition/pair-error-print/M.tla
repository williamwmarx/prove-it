---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
Init == x = 0
Next == (Assert(FALSE,"OPERAND") /\ x' = x) \cdot (PrintT("OPERAND") /\ x' = x)
====
