---- MODULE Spec ----
CONSTANT c, S, F(_)
VARIABLE x, y
f[i \in {1}] == i
op1(a) == a
G(H(_)) == H(x)
M == INSTANCE Inner WITH w <- c
THEOREM T0 == CHOOSE q \in c : f[1]
<1>1. ENABLED ([q \in ({} -+-> f[1]) |-> SF_<<x, y>>(y)])
<1>2. LET L(p) == CASE x -> 1 [] OTHER -> f[1] IN L(ENABLED (1))
  BY <1>1
<1> QED BY <1>2
====
