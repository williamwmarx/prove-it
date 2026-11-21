---- MODULE M ----
EXTENDS Aid, Naturals, TLC
VARIABLE s
Init == s = 0
Next == UNCHANGED s
Inv == s = 0
====
