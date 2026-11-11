---- MODULE M ----
EXTENDS Naturals
CONSTANT F(_)
K == F(7) + 1
VARIABLE x
Init == x = K
Next == x' = x
Inv == x = 5
====
