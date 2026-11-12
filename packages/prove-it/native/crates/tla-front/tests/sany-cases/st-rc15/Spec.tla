---- MODULE Spec ----
ZZ == 1 \star 2
---- MODULE A ----
RECURSIVE R(_)
====
A == LET RECURSIVE G(_)
         G(n) == G(n)
     IN G(1)
====
