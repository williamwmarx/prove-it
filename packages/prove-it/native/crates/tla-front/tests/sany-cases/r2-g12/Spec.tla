---- MODULE Spec ----
A == LET RECURSIVE F(_)
         F(a) == F(a)
         I == INSTANCE Naturals
     IN 1
====
