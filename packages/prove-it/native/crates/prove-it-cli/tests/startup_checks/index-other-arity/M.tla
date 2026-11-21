---- MODULE M ----
EXTENDS Aux, Naturals, TLC
VARIABLE s
Init == s = 0
Next == UNCHANGED s
Inv == Make(1) = 1
====
