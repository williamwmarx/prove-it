---- MODULE M ----
EXTENDS TLC, Naturals
ASSUME PrintT(1 :> 2)
VARIABLE s
Init == s = 0
Next == UNCHANGED s
Inv == TRUE
====
