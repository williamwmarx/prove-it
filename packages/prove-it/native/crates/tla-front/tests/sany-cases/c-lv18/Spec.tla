---- MODULE Spec ----
VARIABLE v
RECURSIVE F(_)
F(x) == IF x THEN F(x') ELSE TRUE
A == F(v)
====
