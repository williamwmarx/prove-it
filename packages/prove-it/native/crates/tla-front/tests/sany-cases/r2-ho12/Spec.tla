---- MODULE Spec ----
VARIABLE x
F(G(_)) == [][G(x)]_x
B == F(LAMBDA a : []a)
====
