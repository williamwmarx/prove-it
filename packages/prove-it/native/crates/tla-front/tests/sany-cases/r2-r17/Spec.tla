---- MODULE Spec ----
A == LET RECURSIVE foo(_)
         I == INSTANCE M
         foo(a) == a
     IN 1
====
