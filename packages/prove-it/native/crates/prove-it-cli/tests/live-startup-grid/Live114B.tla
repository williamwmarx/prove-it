---- MODULE Live114B ----
EXTENDS Naturals
CONSTANT C
VARIABLE x
D == {C}
Q(a) == \A j \in a, k \in D : [](x # j \/ x # k)
In == INSTANCE Live114C WITH K <- C
====
