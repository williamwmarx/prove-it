---- MODULE Spec ----
CONSTANT c, S, F(_)
VARIABLE x, y
f[i \in {1}] == i
op1(a) == a
G(H(_)) == H(x)
M == INSTANCE Inner WITH w <- y'
D0 == ~(UNCHANGED <<x, y>>)
D1 == [x EXCEPT ![[q \in TRUE |-> y]] = <><<f[1]>>_x]
D2 == <>([](M!D(M!E)))
====
