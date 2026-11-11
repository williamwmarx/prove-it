---- MODULE Spec ----
EXTENDS Naturals, STATE
VARIABLE x
Init == x = 0
Next == x' = x
====
