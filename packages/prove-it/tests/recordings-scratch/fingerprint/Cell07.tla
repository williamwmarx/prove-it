---- MODULE Cell07 ----
EXTENDS Naturals, Sequences
CONSTANT M, A_m
VARIABLE x
Init == x = 0
Next == x < 2 /\ x' = x + 1
Inv == x >= 0 => ~([a |-> 1] \in UNION {[{1} -> Nat]})
====
