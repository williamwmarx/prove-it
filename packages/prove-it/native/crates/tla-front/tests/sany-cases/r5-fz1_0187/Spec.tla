---- MODULE Spec ----
EXTENDS Naturals
CONSTANT c, S, F(_), G
VARIABLE x, r, f
Init == x = 0
Next == x' = x
D0 == 1
D1 == LET L(p) == WF_x(UNCHANGED (TRUE ~> Nat)) IN L(\A q : \EE q : SF_{}(<<>>))
D2 == ((\EE q : q \cdot \A q : S) \cdot IF WF_x(c) THEN (x + c) ELSE Nat)
====
