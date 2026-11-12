---- MODULE M ----
EXTENDS Naturals
VARIABLE x
F(y) == y
Apply(G(_), v) == G(v)
A == Apply((F), x)
====
