---- MODULE Spec ----
CONSTANT c, S, F(_)
VARIABLE x, y
f[i \in {1}] == i
op1(a) == a
G(H(_)) == H(x)
M == INSTANCE Inner WITH w <- y'
D0 == (\EE q : ENABLED (S) -+-> F(~(f[1])))
THEOREM T1 == <><<op1(x)>>_x
<1>1. [][~((op1(x) -+-> c))]_x
<1>2. SF_<<x, y>>(WF_x(M!E))
  BY <1>1
<1> QED BY <1>2
D2 == UNCHANGED <<x, y>>
====
