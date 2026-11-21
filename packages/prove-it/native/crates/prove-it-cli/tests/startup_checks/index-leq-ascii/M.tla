---- MODULE M ----
EXTENDS Naturals
VARIABLE s
Init == s = 0
Next == UNCHANGED s
Inv == 1 =< 2
====
