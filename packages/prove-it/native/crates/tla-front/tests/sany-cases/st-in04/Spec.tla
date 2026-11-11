---- MODULE Spec ----
ZZ == 1 \star 2
---- MODULE I ----
f[x \in {1}] == x
====
LOCAL INSTANCE I
A == f[1, 2]
====
