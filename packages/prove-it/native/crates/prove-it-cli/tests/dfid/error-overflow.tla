---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
RECURSIVE F(_)
F(n) == F(n + 1)
Init == x = 0
Next == x < 2 /\ x' = IF x = 1 THEN F(0) ELSE x + 1
====
