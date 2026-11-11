---- MODULE Spec ----
CONSTANT c, S, F(_)
VARIABLE x, y
f[i \in {1}] == i
op1(a) == a
G(H(_)) == H(x)
M == INSTANCE Inner WITH w <- 1
D0 == <><<(\EE q : f[1] ~> SF_<<x, y>>(y))>>_x
D1 == (op1(x) /\ x)
THEOREM T2 == ASSUME NEW CONSTANT v2, <><<{}>>_x PROVE \A q \in F({}) : SF_<<x, y>>(S)
====
