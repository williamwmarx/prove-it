---- MODULE M ----
EXTENDS TLC, Naturals
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 2
G1(i) == 5
Inv == TLCGet(0) = 5
====
