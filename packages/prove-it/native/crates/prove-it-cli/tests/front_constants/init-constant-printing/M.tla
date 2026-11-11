---- MODULE M ----
EXTENDS TLC
VARIABLE x
P == PrintT("marker")
Init == TRUE
Next == x' = x
====
