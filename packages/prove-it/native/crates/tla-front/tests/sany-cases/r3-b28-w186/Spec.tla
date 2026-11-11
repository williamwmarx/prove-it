---- MODULE Spec ----
CONSTANT c, S, F(_)
VARIABLE x, y
f[i \in {1}] == i
op1(a) == a
G(H(_)) == H(x)
M == INSTANCE Inner WITH w <- y'
ASSUME {\A q \in (M!E -+-> M!E) : ~(1), [q \in CHOOSE q \in S : {} |-> ENABLED (f[1])]}
====
