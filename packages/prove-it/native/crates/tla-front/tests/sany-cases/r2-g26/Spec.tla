---- MODULE Spec ----
RECURSIVE F(_, _)
F(a, b) == F(a, b')
G == F(1, 2)
====
