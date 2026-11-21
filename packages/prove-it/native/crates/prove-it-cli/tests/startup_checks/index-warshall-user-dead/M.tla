---- MODULE M ----
EXTENDS TransitiveClosure, Naturals
VARIABLE s
Init == s = 0
Next == UNCHANGED s
Inv == s = 0
====
