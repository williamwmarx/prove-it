---- MODULE Spec ----
F(a, b) == INSTANCE M WITH c <- a
X == F(1) ! !!(4, 6)
====
