---- MODULE Spec ----
EXTENDS Naturals
CONSTANT c, S, F(_), G
VARIABLE x, r, f
Init == x = 0
Next == x' = x
D0 == SF_@([q \in S |-> f[1]])
D1 == (\A q : x' \/ WF_x(Undef))
ASSUME ((Next => "s") ~> {x', q})
====
