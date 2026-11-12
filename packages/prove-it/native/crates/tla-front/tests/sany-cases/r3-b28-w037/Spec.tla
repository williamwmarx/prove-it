---- MODULE Spec ----
CONSTANT c, S, F(_)
VARIABLE x, y
f[i \in {1}] == i
op1(a) == a
G(H(_)) == H(x)
M == INSTANCE Inner WITH w <- y'
D0 == UNCHANGED <<x, y>>
ASSUME (1 /\ {})
THEOREM T2 == ASSUME NEW CONSTANT v2, <>(TRUE) PROVE ENABLED (([x EXCEPT ![M!E] = @] /\ SF_<<x, y>>(S)))
====
