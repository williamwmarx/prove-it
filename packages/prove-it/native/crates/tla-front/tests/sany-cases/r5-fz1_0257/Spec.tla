---- MODULE Spec ----
EXTENDS Naturals
CONSTANT c, S, F(_), G
VARIABLE x, r, f
Init == x = 0
Next == x' = x
D0 == (LET L(p) == @ IN L((TRUE \/ r.a)) \cdot (x' => LET L(p) == x IN L({})))
D1 == ([x EXCEPT ![1] = \A q : [Next]_@] ~> \EE q : [x EXCEPT ![1] = ENABLED (x')])
====
