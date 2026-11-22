---- MODULE M ----
VARIABLE x
RECURSIVE S(_), R(_)
R(p) == S(p)
S(p) == p' = 1 \/ S(p)
====
