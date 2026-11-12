---- MODULE Live104B ----
EXTENDS Naturals, TLC
CONSTANT F(_)
VARIABLE x
Q == \A i \in {F(1)} : [](x # i)
====
