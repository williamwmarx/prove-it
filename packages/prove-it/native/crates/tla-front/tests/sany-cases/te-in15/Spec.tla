---- MODULE Spec ----
---- MODULE I ----
f[x \in {1}] == x
====
M == INSTANCE I
THEOREM M!f[1, 2] = 1
====
