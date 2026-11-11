---- MODULE Spec ----
CONSTANT c, S, F(_)
VARIABLE x, y
f[i \in {1}] == i
op1(a) == a
G(H(_)) == H(x)
M == INSTANCE Inner WITH w <- 1
THEOREM T0 == ASSUME NEW TEMPORAL v0, \A q \in 1 : 1 PROVE SF_<<x, y>>(<><<x>>_x)
D1 == <>(SF_<<x, y>>([](TRUE)))
====
