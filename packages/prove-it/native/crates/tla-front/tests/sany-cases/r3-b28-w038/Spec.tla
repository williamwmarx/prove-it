---- MODULE Spec ----
CONSTANT c, S, F(_)
VARIABLE x, y
f[i \in {1}] == i
op1(a) == a
G(H(_)) == H(x)
M == INSTANCE Inner WITH w <- y'
ASSUME op1(LET L(p) == <><<f[1]>>_x IN L(G(F)))
THEOREM T1 == LET L(p) == S IN L(M!E)
<1>1. [q \in F(TRUE) |-> (x /\ x)]
<1>2. op1(M!E)'
  BY <1>1
<1> QED BY <1>2
====
