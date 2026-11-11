---- MODULE Spec ----
EXTENDS Naturals, STATE, Sequences
VARIABLE x
Init == x = 0
Next == x' = x
====
