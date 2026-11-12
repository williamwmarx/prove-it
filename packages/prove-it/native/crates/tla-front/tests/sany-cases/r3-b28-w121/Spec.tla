---- MODULE Spec ----
CONSTANT c, S, F(_)
VARIABLE x, y
f[i \in {1}] == i
op1(a) == a
G(H(_)) == H(x)
M == INSTANCE Inner WITH w <- 1
THEOREM T0 == ASSUME NEW ACTION v0, ~(y) PROVE (\EE q : 1) \cdot (<><<F(1)>>_x)
ASSUME CHOOSE q \in op1(x) : c
====
