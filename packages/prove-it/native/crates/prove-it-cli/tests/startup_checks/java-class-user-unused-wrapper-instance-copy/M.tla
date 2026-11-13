---- MODULE M ----
EXTENDS TLC, Naturals
VARIABLE x
J == INSTANCE Helper
ASSUME PrintT(TRUE)
Init == x = 0
Next == x' = x
====
