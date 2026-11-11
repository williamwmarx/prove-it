---- MODULE Spec ----
---- MODULE I ----
f[x \in {1}] == x
====
---- MODULE K ----
M == INSTANCE I
====
P == INSTANCE K
A == P!M!f[1, 2]
====
