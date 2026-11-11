---- MODULE Spec ----
CONSTANT c, S, F(_)
VARIABLE x, y
f[i \in {1}] == i
op1(a) == a
G(H(_)) == H(x)
M == INSTANCE Inner WITH w <- x
ASSUME ~((f[1] -+-> M!E))
D1 == (1) \cdot (M!E)
====
