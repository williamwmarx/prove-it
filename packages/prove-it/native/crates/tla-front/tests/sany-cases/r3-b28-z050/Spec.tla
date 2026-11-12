---- MODULE Spec ----
CONSTANT c, S, F(_)
VARIABLE x, y
f[i \in {1}] == i
op1(a) == a
G(H(_)) == H(x)
M == INSTANCE Inner WITH w <- 1
ASSUME <><<M!D(WF_x(TRUE))>>_x
D1 == (F(f[1]) ~> ENABLED (1))
====
