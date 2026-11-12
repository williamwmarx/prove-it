---- MODULE Spec ----
CONSTANT c, S, F(_)
VARIABLE x, y
f[i \in {1}] == i
op1(a) == a
G(H(_)) == H(x)
M == INSTANCE Inner WITH w <- 1
D0 == <<CASE F(S) -> [x EXCEPT ![S] = @] [] OTHER -> <>(x)>>
ASSUME G(op1)
====
