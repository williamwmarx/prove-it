---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
Init == x = 0
Next == LET P == ((PrintT("OPERAND") /\ x' = x) \cdot (x' = x)) IN P
====
