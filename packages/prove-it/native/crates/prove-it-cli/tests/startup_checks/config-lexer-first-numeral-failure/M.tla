---- MODULE M ----
EXTENDS Naturals, TLC
CONSTANT N
VARIABLE x
Init == x = 0
Next == UNCHANGED x
Inv == FALSE
A == PrintT("startup")
ASSUME A
====
