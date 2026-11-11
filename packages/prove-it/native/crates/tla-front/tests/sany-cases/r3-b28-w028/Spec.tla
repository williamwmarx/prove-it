---- MODULE Spec ----
CONSTANT c, S, F(_)
VARIABLE x, y
f[i \in {1}] == i
op1(a) == a
G(H(_)) == H(x)
M == INSTANCE Inner WITH w <- 1
ASSUME <><<op1(1)>>_x
THEOREM T1 == ASSUME NEW  v1, LET L(p) == M!E IN L(op1(x)) PROVE (S /\ M!E)
ASSUME CHOOSE q \in UNCHANGED x : [](c)
====
