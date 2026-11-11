---- MODULE Spec ----
CONSTANT c, S, F(_)
VARIABLE x, y
f[i \in {1}] == i
op1(a) == a
G(H(_)) == H(x)
M == INSTANCE Inner WITH w <- y'
D0 == F(<><<SF_<<x, y>>(F(1))>>_x)
D1 == []([x EXCEPT ![\A q \in {} : S] = @])
D2 == <>(TRUE)
====
