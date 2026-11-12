---- MODULE Spec ----
EXTENDS Naturals
CONSTANT c, S, F(_), G
VARIABLE x, r, f
Init == x = 0
Next == x' = x
D0 == IF Undef THEN (CHOOSE q \in \E q \in x : Undef : [x EXCEPT ![1] = Init] + (ENABLED (r.a))') ELSE r.a
D1 == [WF_x(c)]_{UNCHANGED Init, q}
D2 == ((q \/ S))'
====
