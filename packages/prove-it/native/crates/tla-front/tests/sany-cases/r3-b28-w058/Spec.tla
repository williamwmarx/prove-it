---- MODULE Spec ----
CONSTANT c, S, F(_)
VARIABLE x, y
f[i \in {1}] == i
op1(a) == a
G(H(_)) == H(x)
M == INSTANCE Inner WITH w <- x
THEOREM T0 == ASSUME NEW ACTION v0, [](f[1]) PROVE op1(y)
ASSUME {op1(CHOOSE q \in {} : S), \EE q : <>(c)}
====
