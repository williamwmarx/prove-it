---- MODULE Spec ----
CONSTANT c, S, F(_)
VARIABLE x, y
f[i \in {1}] == i
op1(a) == a
G(H(_)) == H(x)
M == INSTANCE Inner WITH w <- c
THEOREM T0 == ASSUME NEW TEMPORAL v0, CASE TRUE -> M!E [] OTHER -> x PROVE {[q \in {c, x} |-> (F(1) -+-> x)], ENABLED (~(1))}
D1 == (<<x>> ~> \E q : {})
THEOREM T2 == \EE q : c
<1>1. <<{{x, {}}, S'}>>
<1>2. (F(c)) \cdot ([a |-> TRUE, b |-> y])
  BY <1>1
<1> QED BY <1>2
====
