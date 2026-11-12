---- MODULE Spec ----
CONSTANT c, S, F(_)
VARIABLE x, y
f[i \in {1}] == i
op1(a) == a
G(H(_)) == H(x)
M == INSTANCE Inner WITH w <- 1
THEOREM T0 == [][{}]_x
<1>1. SF_<<x, y>>(~(\A q \in {} : f[1]))
<1>2. WF_x(SF_<<x, y>>(M!E))
  BY <1>1
<1> QED BY <1>2
D1 == (TRUE \in op1(x))
ASSUME CASE x -> op1(x) [] OTHER -> f[1]
====
