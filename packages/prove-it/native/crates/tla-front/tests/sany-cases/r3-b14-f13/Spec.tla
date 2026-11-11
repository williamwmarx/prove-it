---- MODULE Spec ----
VARIABLE x
f[a \in {1}] == a
B == f[1, 2]'
C == f[zz, 2]
====
