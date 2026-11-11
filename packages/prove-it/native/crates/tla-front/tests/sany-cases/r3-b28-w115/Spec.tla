---- MODULE Spec ----
CONSTANT c, S, F(_)
VARIABLE x, y
f[i \in {1}] == i
op1(a) == a
G(H(_)) == H(x)
M == INSTANCE Inner WITH w <- y'
D0 == [a |-> \EE q : c, b |-> <>(M!E)]
D1 == <<(1 ~> S)>>
D2 == ENABLED (<><<UNCHANGED <<x, y>>>>_x)
====
