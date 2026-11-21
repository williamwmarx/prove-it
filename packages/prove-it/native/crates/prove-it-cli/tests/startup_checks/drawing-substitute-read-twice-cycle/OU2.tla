---- MODULE OU2 ----
EXTENDS TLC
CONSTANT c
C3 == PrintT(c) /\ PrintT(c)
====
