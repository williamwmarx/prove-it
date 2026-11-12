---- MODULE Spec ----
CONSTANT c, S, F(_)
VARIABLE x, y
f[i \in {1}] == i
op1(a) == a
G(H(_)) == H(x)
M == INSTANCE Inner WITH w <- 1
THEOREM T0 == UNCHANGED <<x, y>>
<1>1. \A q \in [a |-> [][M!E]_(y), b |-> \A q \in x : op1(x)] : [][M!D(f[1])]_((M!E ~> f[1]))
<1>2. F((TRUE) \cdot (x))
  BY <1>1
<1> QED BY <1>2
D1 == op1(x)'
====
