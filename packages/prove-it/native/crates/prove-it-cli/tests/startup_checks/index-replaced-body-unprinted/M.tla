---- MODULE M ----
EXTENDS Aux, Naturals, TLC
VARIABLE s
Init == s = 0
Next == UNCHANGED s
Inv == s = 0
====
