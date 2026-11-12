---- MODULE Spec ----
EXTENDS J
ZZ == 1 \star 2
---- MODULE A ----
---- MODULE B ----
RECURSIVE R(_)
====
====
RECURSIVE F(_)
F(n) == F(n)
RECURSIVE G(_)
====
