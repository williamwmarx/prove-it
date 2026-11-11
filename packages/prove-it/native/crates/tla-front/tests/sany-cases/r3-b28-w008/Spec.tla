---- MODULE Spec ----
CONSTANT c, S, F(_)
VARIABLE x, y
f[i \in {1}] == i
op1(a) == a
G(H(_)) == H(x)
M == INSTANCE Inner WITH w <- 1
D0 == <>({(f[1] -+-> c), F(1)})
ASSUME CASE <><<[](op1(x))>>_x -> SF_<<x, y>>((op1(x) -+-> F(1))) [] OTHER -> CASE ({} /\ TRUE) -> {f[1], S} [] OTHER -> [](F(1))
THEOREM T2 == ASSUME NEW ACTION v2, \EE q : F(1) PROVE ENABLED ({<>(c), (c => y)})
====
