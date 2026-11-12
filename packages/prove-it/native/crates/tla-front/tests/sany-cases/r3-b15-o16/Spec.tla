---- MODULE Spec ----
VARIABLE x
B == LET RECURSIVE a(_)
         z == 1
         RECURSIVE b(_, _)
         a(n) == 1
         b(n) == 2
     IN a(1)
====
