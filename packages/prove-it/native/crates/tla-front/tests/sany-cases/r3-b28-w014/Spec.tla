---- MODULE Spec ----
CONSTANT c, S, F(_)
VARIABLE x, y
f[i \in {1}] == i
op1(a) == a
G(H(_)) == H(x)
M == INSTANCE Inner WITH w <- 1
THEOREM T0 == ASSUME NEW ACTION v0, \A q \in y : f[1] PROVE UNCHANGED x
THEOREM T1 == WF_x(y)
<1>1. (SF_<<x, y>>({}) \in (y -+-> TRUE))
<1>2. [][LET L(p) == M!E IN L(S)]_x
  BY <1>1
<1> QED BY <1>2
====
