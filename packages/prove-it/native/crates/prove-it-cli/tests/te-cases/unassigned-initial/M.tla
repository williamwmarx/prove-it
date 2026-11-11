---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLES x, y
Init == x = 0
Next == x' = x + 1 /\ y' = 0
====
