---- MODULE Spec ----
CONSTANT c, S, F(_)
VARIABLE x, y
f[i \in {1}] == i
op1(a) == a
G(H(_)) == H(x)
M == INSTANCE Inner WITH w <- c
ASSUME <><<M!E>>_x
D1 == [](1')
D2 == UNCHANGED x
====
