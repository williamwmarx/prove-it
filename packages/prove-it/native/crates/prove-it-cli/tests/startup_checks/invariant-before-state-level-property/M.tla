---- MODULE M ----
EXTENDS Naturals, TLC, Sequences
VARIABLE x
Init == x = 0
Next == x < 2 /\ x' = x + 1
A == 1 = 1
P == x >= 0
Q == Append(<<1>>, 2)
====
