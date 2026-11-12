---- MODULE Spec ----
CONSTANT c, S, F(_)
VARIABLE x, y
f[i \in {1}] == i
op1(a) == a
G(H(_)) == H(x)
M == INSTANCE Inner WITH w <- c
D0 == SF_<<x, y>>(F({}))
THEOREM T1 == ASSUME NEW  v1, [x EXCEPT ![TRUE] = M!E] PROVE {op1({})', [a |-> (S -+-> TRUE), b |-> [a |-> x, b |-> 1]]}
D2 == F(WF_x({}))
====
