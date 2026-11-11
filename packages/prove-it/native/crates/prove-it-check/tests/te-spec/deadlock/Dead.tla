---- MODULE Dead ----
EXTENDS Naturals
VARIABLES x, y
Init == x = 0 /\ y = "a"
Next == x < 2 /\ x' = x + 1 /\ y' = y
====
