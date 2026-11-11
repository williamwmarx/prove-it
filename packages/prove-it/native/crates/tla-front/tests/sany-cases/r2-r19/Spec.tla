---- MODULE Spec ----
A == LET RECURSIVE foo(_)
         foo(a) == \A foo \in {} : TRUE
     IN 1
====
