---- MODULE Spec ----
RECURSIVE f
f[a \in {1}] == f[a, a]
====
