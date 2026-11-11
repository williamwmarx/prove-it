---- MODULE M ----
EXTENDS Naturals, Sequences, TLC
VARIABLE x
Init == x = 0
Next == x < 2 /\ x' = x + 1
P == LET Q == 1 IN Q
====
