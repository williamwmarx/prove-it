---- MODULE Spec ----
A == LET RECURSIVE foo(_)
         foo(a) == LET RECURSIVE bar
                       bar == 1
                   IN 1
     IN 1
====
