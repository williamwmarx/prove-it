---- MODULE M ----
EXTENDS Aid, Naturals, TLC
K == PrintT(Make)
VARIABLE s
Init == s = 0
Next == UNCHANGED s
Inv == s = 0
====
