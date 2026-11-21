---- MODULE M ----
EXTENDS Naturals
VARIABLES z, x, y
Init == x = 0
Next == /\ x' = x /\ y' = y /\ z' = z
====
