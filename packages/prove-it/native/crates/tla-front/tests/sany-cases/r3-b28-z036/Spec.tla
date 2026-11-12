---- MODULE Spec ----
CONSTANT c, S, F(_)
VARIABLE x, y
f[i \in {1}] == i
op1(a) == a
G(H(_)) == H(x)
M == INSTANCE Inner WITH w <- y'
D0 == WF_x(\E q : [][x]_x)
D1 == ([x EXCEPT ![S] = @]) \cdot ([](x))
====
