---- MODULE Spec ----
RECURSIVE F(_)
F(a) == LET G == F(a)' IN G
====
