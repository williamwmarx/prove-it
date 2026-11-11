---- MODULE Spec ----
a == 1
RECURSIVE F(_), G(_)
F(n) == G(n)
G(n) == F(n)
R == [a |-> F(1)]
====
