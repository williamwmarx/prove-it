---- MODULE Spec ----
CONSTANT c, S, F(_)
VARIABLE x, y
f[i \in {1}] == i
op1(a) == a
G(H(_)) == H(x)
M == INSTANCE Inner WITH w <- 1
D0 == <>((G(F) => \E q : f[1]))
D1 == LET L(p) == \E q : TRUE IN L(SF_<<x, y>>(M!E))
THEOREM T2 == \A q \in x : y
<1>1. CHOOSE q \in UNCHANGED (M!E') : ~(F(1)')
<1>2. LET L(p) == (S => c) IN L(IF S THEN {} ELSE c)
  BY <1>1
<1> QED BY <1>2
====
