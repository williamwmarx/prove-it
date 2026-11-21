---- MODULE M ----
EXTENDS TLC, Naturals
ASSUME PrintT(<<1 :> 2, 3>>)
VARIABLE x
Init == x = 0
Next == x' = x
====
