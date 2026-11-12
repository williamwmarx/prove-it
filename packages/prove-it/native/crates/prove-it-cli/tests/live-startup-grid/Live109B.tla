---- MODULE Live109B ----
EXTENDS Naturals
CONSTANT C
VARIABLE x
D == {C}
Q(Op(_)) == \A j \in Op(1) : [](x # j)
====
