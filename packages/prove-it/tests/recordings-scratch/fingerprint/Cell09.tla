---- MODULE Cell09 ----
EXTENDS Naturals, Sequences
CONSTANT M, A_m
VARIABLE x
Init == x = 0
Next == x < 2 /\ x' = x + 1
Inv == x >= 0 => ~(3 \in UNION {Seq({1})})
====
