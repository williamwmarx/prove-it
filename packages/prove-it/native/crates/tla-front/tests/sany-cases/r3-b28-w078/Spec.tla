---- MODULE Spec ----
CONSTANT c, S, F(_)
VARIABLE x, y
f[i \in {1}] == i
op1(a) == a
G(H(_)) == H(x)
M == INSTANCE Inner WITH w <- y'
D0 == (S) \cdot (f[1])
D1 == SF_<<x, y>>(M!E)
ASSUME \E q : x
====
