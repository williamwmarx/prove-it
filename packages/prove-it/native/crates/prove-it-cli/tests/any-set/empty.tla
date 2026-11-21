---- MODULE M ----
EXTENDS TLC, Naturals
VARIABLE x
Init == x = 0
Next == x' = x
Inv == [Any -> {}] = {}
====
