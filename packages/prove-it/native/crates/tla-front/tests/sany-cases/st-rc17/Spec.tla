---- MODULE Spec ----
ZZ == 1 \star 2
---- MODULE A ----
---- MODULE B ----
RECURSIVE R(_)
====
====
A == LET RECURSIVE G(_)
     IN 1
====
