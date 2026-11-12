---- MODULE Spec ----
CONSTANT c, S, F(_)
VARIABLE x, y
f[i \in {1}] == i
op1(a) == a
G(H(_)) == H(x)
M == INSTANCE Inner WITH w <- x
D0 == \EE q : M!E
D1 == {\E q : SF_<<x, y>>(op1(x)), [a |-> <>(M!E), b |-> M!D(f[1])]}
====
