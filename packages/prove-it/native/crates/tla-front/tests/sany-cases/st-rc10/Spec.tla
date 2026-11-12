---- MODULE Spec ----
ZZ == 1 \star 2
---- MODULE Inner ----
RECURSIVE R(_), S(_)
====
RECURSIVE F(_)
F(n) == F(n)
====
