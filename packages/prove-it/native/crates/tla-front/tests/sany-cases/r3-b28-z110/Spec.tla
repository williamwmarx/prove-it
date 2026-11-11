---- MODULE Spec ----
CONSTANT c, S, F(_)
VARIABLE x, y
f[i \in {1}] == i
op1(a) == a
G(H(_)) == H(x)
M == INSTANCE Inner WITH w <- 1
THEOREM T0 == \EE q : {}
<1>1. G(LAMBDA p : M!D(1))
<1>2. ((F(1)) \cdot (c) -+-> S')
  BY <1>1
<1> QED BY <1>2
====
