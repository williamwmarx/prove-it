---- MODULE Spec ----
CONSTANT c, S, F(_)
VARIABLE x, y
f[i \in {1}] == i
op1(a) == a
G(H(_)) == H(x)
M == INSTANCE Inner WITH w <- x
D0 == <>(S)
THEOREM T1 == (f[1] => x)
<1>1. IF op1(x) THEN M!E ELSE op1(x)
<1>2. CHOOSE q \in (TRUE -+-> {}) : (f[1] ~> f[1])
  BY <1>1
<1> QED BY <1>2
====
