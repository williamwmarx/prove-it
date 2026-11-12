---- MODULE Spec ----
CONSTANT c, S, F(_)
VARIABLE x, y
f[i \in {1}] == i
op1(a) == a
G(H(_)) == H(x)
M == INSTANCE Inner WITH w <- 1
THEOREM T0 == ({}) \cdot (x)
<1>1. ~(<><<1>>_x)
<1>2. op1([f EXCEPT ![x] = x])
  BY <1>1
<1> QED BY <1>2
ASSUME (~(<<F(1)>>) ~> [a |-> 1', b |-> ENABLED (y)])
D2 == ~([]([q \in f[1] |-> op1(x)]))
====
