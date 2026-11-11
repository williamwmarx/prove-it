---- MODULE Spec ----
VARIABLE x
Init == x = 0
Next == x' = x
A(F(_), _ +) == 1
====
