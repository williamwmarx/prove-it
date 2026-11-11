---- MODULE M ----
EXTENDS Naturals
CONSTANT F(_)
ASSUME F(1) = 4
VARIABLE x
Init == x = 0
Next == x' = x
====
