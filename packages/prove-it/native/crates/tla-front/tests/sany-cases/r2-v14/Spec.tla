---- MODULE Spec ----
VARIABLE x
A == [](x = 1)
B == A'
C == ENABLED A
D == UNCHANGED A
====
