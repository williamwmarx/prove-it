---- MODULE Spec ----
CONSTANT c, S, F(_)
VARIABLE x, y
f[i \in {1}] == i
op1(a) == a
G(H(_)) == H(x)
M == INSTANCE Inner WITH w <- y'
ASSUME (SF_<<x, y>>(TRUE) \in LET L(p) == F(1) IN L(f[1]))
ASSUME (f[1] -+-> {})
ASSUME M!D(~((y) \cdot (y)))
====
