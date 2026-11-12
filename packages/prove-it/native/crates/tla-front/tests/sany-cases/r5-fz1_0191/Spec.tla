---- MODULE Spec ----
EXTENDS Naturals
CONSTANT c, S, F(_), G
VARIABLE x, r, f
Init == x = 0
Next == x' = x
D0 == r.a
D1 == {[q \in []ENABLED (c) |-> "s"], \A q : (f[1] + \EE q : <<>>)}
D2 == (CHOOSE q \in []q : [x']_{})'
THEOREM ([x EXCEPT ![1] = x'] + 1)
====
