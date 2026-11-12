---- MODULE Spec ----
EXTENDS A
VARIABLE x
Init == x = 0
Next == x' = x
---- MODULE Inner ----
EXTENDS C
I == INSTANCE G
====

====
