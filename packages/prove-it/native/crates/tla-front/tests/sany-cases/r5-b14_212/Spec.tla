---- MODULE Spec ----
VARIABLE x
Init == x = 0
Next == x' = x
A == LET B(_ $) == 1 IN 1
====
