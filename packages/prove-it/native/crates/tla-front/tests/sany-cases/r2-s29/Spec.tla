---- MODULE Spec ----
F(G(_)) == G(1)
A == F(LAMBDA X : X)
B == A!1!(1, 2)
C == A!1!@
====
