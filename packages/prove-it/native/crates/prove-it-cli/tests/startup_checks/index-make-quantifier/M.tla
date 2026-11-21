---- MODULE M ----
EXTENDS Aid, Naturals
VARIABLE s
Init == s = 0
Next == UNCHANGED s
Inv == \A i \in {1} : Make
====
