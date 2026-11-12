---- MODULE Spec ----
VARIABLE x
Init == x = 0
Next == x' = x
A == /\ x = 1  /\ Undef
====
