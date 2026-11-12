---- MODULE Spec ----
CONSTANT c, S, F(_)
VARIABLE x, y
f[i \in {1}] == i
op1(a) == a
G(H(_)) == H(x)
M == INSTANCE Inner WITH w <- x
THEOREM T0 == \EE q : 1
<1>1. <<F(1)>>
<1>2. CHOOSE q \in UNCHANGED x : WF_x(S)
  BY <1>1
<1> QED BY <1>2
====
