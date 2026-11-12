---- MODULE Spec ----
CONSTANT c, S, F(_)
VARIABLE x, y
f[i \in {1}] == i
op1(a) == a
G(H(_)) == H(x)
M == INSTANCE Inner WITH w <- c
THEOREM T0 == ASSUME NEW CONSTANT v0, F(1) PROVE [f EXCEPT ![LET L(p) == {} IN L(S)] = LET L(p) == x IN L(F(1))]
D1 == <<\E q : WF_x(S)>>
====
