---- MODULE Spec ----
CONSTANT c, S, F(_)
VARIABLE x, y
f[i \in {1}] == i
op1(a) == a
G(H(_)) == H(x)
M == INSTANCE Inner WITH w <- y'
D0 == WF_x([f EXCEPT ![\A q \in M!E : y] = @])
THEOREM T1 == [][{}]_x
<1>1. UNCHANGED x
<1>2. op1({{}, TRUE})
  BY <1>1
<1> QED BY <1>2
====
