---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLES x, y
Init == x = 0 /\ y = 0
A == x' = x /\ y' = y
B == x' = x
Next == A \/ B
====
