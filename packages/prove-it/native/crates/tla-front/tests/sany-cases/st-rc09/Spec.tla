---- MODULE Spec ----
ZZ == 1 \star 2
---- MODULE Inner ----
RECURSIVE R(_)
====
RECURSIVE F(_), G(_)
F(n) == G(n)
====
