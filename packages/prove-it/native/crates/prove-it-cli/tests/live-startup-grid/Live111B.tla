---- MODULE Live111B ----
EXTENDS Naturals
CONSTANT C
VARIABLE x
D == {C}
Q(a) == \A j \in a : [](x # j)
R == Q(D)
====
