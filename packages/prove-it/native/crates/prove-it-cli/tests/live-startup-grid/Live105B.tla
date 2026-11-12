---- MODULE Live105B ----
EXTENDS Naturals, TLC
VARIABLE x
SN == {}
Q == \A i \in SN : [](x # i)
====
