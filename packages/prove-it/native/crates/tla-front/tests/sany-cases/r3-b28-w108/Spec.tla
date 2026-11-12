---- MODULE Spec ----
CONSTANT c, S, F(_)
VARIABLE x, y
f[i \in {1}] == i
op1(a) == a
G(H(_)) == H(x)
M == INSTANCE Inner WITH w <- y'
THEOREM T0 == UNCHANGED (M!E)
<1>1. <>(IF S THEN TRUE ELSE y)
<1>2. F(SF_<<x, y>>(c))
  BY <1>1
<1> QED BY <1>2
D1 == M!D(F(1))
====
