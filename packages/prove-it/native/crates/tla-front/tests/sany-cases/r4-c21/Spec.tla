---- MODULE Spec ----
F(a,b) == TRUE
M == INSTANCE I WITH (+) <- F
B == M!X(1)
C == M!\oplus
====
