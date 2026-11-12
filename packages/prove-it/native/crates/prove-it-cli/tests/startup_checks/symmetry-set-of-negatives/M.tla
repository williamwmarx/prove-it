---- MODULE M ----
EXTENDS Integers, Sequences, TLC
VARIABLE x
Init == x = 0
Next == x < 2 /\ x' = x + 1
P == {-1}
====
