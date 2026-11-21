---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
Init == x = 0
Next == IF x = 0 THEN ((Assert(FALSE,"OPERAND") /\ x' = x) \cdot (x' = x)) ELSE UNCHANGED x
====
