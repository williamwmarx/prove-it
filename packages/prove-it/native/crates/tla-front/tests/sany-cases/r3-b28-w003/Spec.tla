---- MODULE Spec ----
CONSTANT c, S, F(_)
VARIABLE x, y
f[i \in {1}] == i
op1(a) == a
G(H(_)) == H(x)
M == INSTANCE Inner WITH w <- y'
D0 == (<<M!D(F(1))>> ~> G(LAMBDA p : op1({})))
THEOREM T1 == ASSUME NEW TEMPORAL v1, op1(M!E) PROVE (CHOOSE q \in op1(x) : TRUE \in ~(F(1)))
D2 == op1((op1(x) \in M!E))
====
