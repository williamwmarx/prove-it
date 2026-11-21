---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x = 0
Next == PrintT(TLCGet("level")) /\ x' = IF x < 2 THEN x + 1 ELSE x
====
