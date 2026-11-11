---- MODULE Spec ----
EXTENDS A, B
VARIABLE x
Init == x = 0
Next == x' = x
---- MODULE Inner ----
EXTENDS C
====

====
