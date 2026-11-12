---- MODULE Spec ----
CONSTANT c, S, F(_)
VARIABLE x, y
f[i \in {1}] == i
op1(a) == a
G(H(_)) == H(x)
M == INSTANCE Inner WITH w <- y'
ASSUME (WF_x(y') /\ (op1(c) /\ IF f[1] THEN M!E ELSE F(1)))
THEOREM T1 == ASSUME NEW CONSTANT v1, LET L(p) == y IN L(c) PROVE \EE q : f[1]
====
