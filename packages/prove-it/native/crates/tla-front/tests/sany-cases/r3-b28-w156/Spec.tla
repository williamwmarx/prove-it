---- MODULE Spec ----
CONSTANT c, S, F(_)
VARIABLE x, y
f[i \in {1}] == i
op1(a) == a
G(H(_)) == H(x)
M == INSTANCE Inner WITH w <- y'
THEOREM T0 == UNCHANGED x
<1>1. UNCHANGED x
<1>2. []({op1(x), M!E})
  BY <1>1
<1> QED BY <1>2
THEOREM T1 == [a |-> y, b |-> x]
<1>1. (c => y)
<1>2. <<TRUE>>'
  BY <1>1
<1> QED BY <1>2
ASSUME WF_x([q \in op1(x) |-> {}])
====
