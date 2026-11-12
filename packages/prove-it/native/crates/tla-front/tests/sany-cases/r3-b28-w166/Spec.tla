---- MODULE Spec ----
CONSTANT c, S, F(_)
VARIABLE x, y
f[i \in {1}] == i
op1(a) == a
G(H(_)) == H(x)
M == INSTANCE Inner WITH w <- y'
D0 == UNCHANGED (({} \in S))
THEOREM T1 == UNCHANGED x
<1>1. UNCHANGED ([][f[1]]_x)
<1>2. (op1(1) ~> LET L(p) == f[1] IN L(x))
  BY <1>1
<1> QED BY <1>2
====
