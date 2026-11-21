---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
Init == x = 0
Next == (1) \cdot (Assert(FALSE,"OPERAND") /\ x' = x)
====
