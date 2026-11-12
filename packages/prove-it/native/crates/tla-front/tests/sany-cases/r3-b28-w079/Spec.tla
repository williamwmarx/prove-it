---- MODULE Spec ----
CONSTANT c, S, F(_)
VARIABLE x, y
f[i \in {1}] == i
op1(a) == a
G(H(_)) == H(x)
M == INSTANCE Inner WITH w <- y'
THEOREM T0 == ASSUME NEW  v0, [a |-> F(1), b |-> f[1]] PROVE ~({})
THEOREM T1 == ASSUME NEW CONSTANT v1, M!E' PROVE M!D(TRUE)
THEOREM T2 == ASSUME NEW ACTION v2, ~(op1(x)) PROVE ENABLED (\EE q : 1)
====
