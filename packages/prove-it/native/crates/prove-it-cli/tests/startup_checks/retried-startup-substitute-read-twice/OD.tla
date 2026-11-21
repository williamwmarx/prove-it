---- MODULE OD ----
EXTENDS TLC
CONSTANT c
C3 == PrintT(c) /\ PrintT(c)
====
