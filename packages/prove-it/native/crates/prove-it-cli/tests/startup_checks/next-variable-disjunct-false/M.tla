---- MODULE M ----
EXTENDS Naturals
VARIABLE x
Init == x = FALSE
Next == x \/ x' = x
====
