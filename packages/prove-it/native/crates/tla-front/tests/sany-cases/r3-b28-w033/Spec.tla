---- MODULE Spec ----
CONSTANT c, S, F(_)
VARIABLE x, y
f[i \in {1}] == i
op1(a) == a
G(H(_)) == H(x)
M == INSTANCE Inner WITH w <- 1
ASSUME \EE q : (CASE x -> 1 [] OTHER -> y /\ SF_<<x, y>>(M!E))
D1 == ([][(M!E \in TRUE)]_<<x,y>> ~> [q \in UNCHANGED <<x, y>> |-> <>(op1(x))])
THEOREM T2 == {F(1), S}
<1>1. WF_x([q \in [](1) |-> M!D({})])
<1>2. \A q \in [a |-> c, b |-> c] : <<op1(x)>>
  BY <1>1
<1> QED BY <1>2
====
