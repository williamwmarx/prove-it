---- MODULE Spec ----
EXTENDS Naturals
CONSTANT c, S, F(_), G
VARIABLE x, r, f
Init == x = 0
Next == x' = x
D0 == SF_{(S ~> q), [q \in c |-> 1]}({})
D1 == "s"
D2 == {"s", WF_x(CHOOSE q \in ENABLED (q) : {})}
ASSUME (F(1) /\ {})
====
