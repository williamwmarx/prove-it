---- MODULE Spec ----
---- MODULE I ----
f[<<x, y>> \in {1}] == x
====
M == INSTANCE I
A == M!f[1, 2]
====
