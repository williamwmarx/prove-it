---- MODULE Cell05 ----
EXTENDS Naturals, Sequences
CONSTANT M, A_m
VARIABLE x
Init == x = 0
Next == x < 2 /\ x' = x + 1
Inv == x >= 0 => ~(<<1>> \in SUBSET {1})
====
