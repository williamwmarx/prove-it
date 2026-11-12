---- MODULE Spec ----
EXTENDS Naturals
CONSTANT c, S, F(_), G
VARIABLE x, r, f
Init == x = 0
Next == x' = x
D0 == {f[1], F(1)}
D1 == ((LET L(p) == LET L(p) == Nat IN L(TRUE) IN L([x EXCEPT ![1] = r.a]) \/ UNCHANGED [F(x')]_@) ~> @)
ASSUME <<(TRUE \/ f[1])>>_x
THEOREM S
====
