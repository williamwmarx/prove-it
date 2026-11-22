---- MODULE M ----
VARIABLE x
RECURSIVE R(_), S(_)
R(p) == S(p)
S(p) == p' = 1 \/ S(p)
C == {[]x}
====
