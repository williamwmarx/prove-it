---- MODULE Spec ----
CONSTANT c, S, F(_)
VARIABLE x, y
f[i \in {1}] == i
op1(a) == a
G(H(_)) == H(x)
M == INSTANCE Inner WITH w <- c
THEOREM T0 == (y -+-> F(1))
<1>1. {[f EXCEPT ![F(1)] = f[1]], [a |-> S, b |-> y]}
<1>2. (<><<{}>>_x /\ (op1(x) -+-> M!E))
  BY <1>1
<1> QED BY <1>2
D1 == M!D(S)
====
