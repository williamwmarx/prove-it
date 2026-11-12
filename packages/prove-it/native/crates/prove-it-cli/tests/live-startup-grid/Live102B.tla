---- MODULE Live102B ----
EXTENDS Naturals, TLC
CONSTANT N
VARIABLE x
SN == {N}
S2 == {2}
Q == \A i \in SN : [](x # i)
====
