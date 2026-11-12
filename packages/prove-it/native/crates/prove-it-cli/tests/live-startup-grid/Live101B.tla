---- MODULE Live101B ----
EXTENDS Naturals, TLC
CONSTANT N
VARIABLE x
SN == {N}
S2 == {2}
Q == \A i \in {N} : [](x # i)
====
