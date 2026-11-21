---- MODULE M ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x < 2 /\ x' = x + 1
P == x < 2
Q == TRUE
====
