---- MODULE M ----
EXTENDS Naturals
VARIABLE x
CONSTANT c
Init == x = TRUE
Next == x' = x \/ c
====
