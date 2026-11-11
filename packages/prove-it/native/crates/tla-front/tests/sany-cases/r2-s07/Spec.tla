---- MODULE Spec ----
F(G(_)) == G(1)
A == F(LAMBDA X : X + 1)
B == A!1!1
====
