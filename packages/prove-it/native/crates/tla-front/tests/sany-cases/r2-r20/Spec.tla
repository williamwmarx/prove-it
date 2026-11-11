---- MODULE Spec ----
A == LET RECURSIVE foo(_)
         foo(G(_)) == 1
     IN 1
====
