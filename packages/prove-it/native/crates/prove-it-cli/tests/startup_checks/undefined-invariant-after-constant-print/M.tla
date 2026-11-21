---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
D == PrintT("d")
Init == x = 0
Next == UNCHANGED x
====
