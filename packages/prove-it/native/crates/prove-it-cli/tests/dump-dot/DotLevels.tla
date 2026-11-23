---- MODULE DotLevels ----
EXTENDS Naturals
VARIABLES p, q
Init == p = 0 /\ q = 0
Next == \/ p < 12 /\ p' = p + 1 /\ q' = q
        \/ q < 12 /\ q' = q + 1 /\ p' = p
====
