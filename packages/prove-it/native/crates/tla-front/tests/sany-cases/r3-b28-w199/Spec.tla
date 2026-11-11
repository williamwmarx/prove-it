---- MODULE Spec ----
CONSTANT c, S, F(_)
VARIABLE x, y
f[i \in {1}] == i
op1(a) == a
G(H(_)) == H(x)
M == INSTANCE Inner WITH w <- y'
D0 == y'
THEOREM T1 == <>(TRUE)
<1>1. F(S')
<1>2. (CHOOSE q \in TRUE : F(1) -+-> SF_<<x, y>>(S))
  BY <1>1
<1> QED BY <1>2
====
