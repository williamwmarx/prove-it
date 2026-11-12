---- MODULE Live112B ----
EXTENDS Naturals
CONSTANT C
VARIABLE x
D == {C}
Snd(a) == D
Q(Op(_)) == \A j \in Op({1}) : [](x # j)
====
