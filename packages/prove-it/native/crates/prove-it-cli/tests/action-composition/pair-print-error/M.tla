---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
Init == x = 0
Next == (PrintT("OPERAND") /\ x' = x) \cdot (Assert(FALSE,"OPERAND") /\ x' = x)
====
