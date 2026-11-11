---- MODULE Spec ----
EXTENDS Naturals
CONSTANT c, S, F(_), G
VARIABLE x, r, f
Init == x = 0
Next == x' = x
D0 == (Undef ~> {})
D1 == IF x THEN Init ELSE c
ASSUME SF_[x EXCEPT ![1] = "s"](CHOOSE q \in "s" : Nat)
====
