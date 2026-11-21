---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLES z, x, y
Init == z = 0 /\ x = 0 /\ y = 0
Next == x = 0
====
