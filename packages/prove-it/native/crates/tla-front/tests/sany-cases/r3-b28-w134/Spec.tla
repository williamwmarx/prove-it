---- MODULE Spec ----
CONSTANT c, S, F(_)
VARIABLE x, y
f[i \in {1}] == i
op1(a) == a
G(H(_)) == H(x)
M == INSTANCE Inner WITH w <- c
D0 == CASE M!D(S) -> \E q : c [] OTHER -> <><<op1(x)>>_x
ASSUME [f EXCEPT ![[][op1(x)]_x] = (TRUE /\ 1)]
====
