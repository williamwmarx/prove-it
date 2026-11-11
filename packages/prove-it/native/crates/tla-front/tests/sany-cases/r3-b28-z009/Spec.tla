---- MODULE Spec ----
CONSTANT c, S, F(_)
VARIABLE x, y
f[i \in {1}] == i
op1(a) == a
G(H(_)) == H(x)
M == INSTANCE Inner WITH w <- 1
THEOREM T0 == ASSUME NEW TEMPORAL v0, CASE F(1) -> F(1) [] OTHER -> S PROVE <<\EE q : [](S)>>
ASSUME IF SF_<<x, y>>(\E q : x) THEN IF UNCHANGED <<x, y>> THEN IF f[1] THEN c ELSE S ELSE {c, x} ELSE <>(\E q : op1(x))
D2 == <>(S)
====
