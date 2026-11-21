---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
RECURSIVE F(_)
F(n) == F(n + 1)
C == F(0)
Init == x = C
Next == x' = x
====
