---- MODULE Spec ----
VARIABLE x
B == LET RECURSIVE u(_) 
         v == LET RECURSIVE w(_) IN 1
     IN 1
====
