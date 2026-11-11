---- MODULE Spec ----
CONSTANT c, S, F(_)
VARIABLE x, y
f[i \in {1}] == i
op1(a) == a
G(H(_)) == H(x)
M == INSTANCE Inner WITH w <- c
D0 == [](ENABLED (S))
D1 == (<><<F({})>>_x ~> [](WF_x(f[1])))
THEOREM T2 == <><<TRUE>>_x
<1>1. G(op1)
<1>2. \A q \in [](op1(x)) : ENABLED (S)
  BY <1>1
<1> QED BY <1>2
====
