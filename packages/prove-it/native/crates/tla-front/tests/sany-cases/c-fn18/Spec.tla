---- MODULE Spec ----
---- MODULE I ----
f[x \in {1}] == x
====
M == INSTANCE I
A == M!f[1, 2]
====
