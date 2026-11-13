---- MODULE M ----
EXTENDS Naturals
VARIABLE x
RECURSIVE Z
Z == <<x, Z>>
Spec == x = 0 /\ [][x' = x]_<<x, Z>>
====
