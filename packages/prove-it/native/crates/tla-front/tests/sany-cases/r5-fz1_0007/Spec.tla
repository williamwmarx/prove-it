---- MODULE Spec ----
EXTENDS Naturals
CONSTANT c, S, F(_), G
VARIABLE x, r, f
Init == x = 0
Next == x' = x
D0 == (S + SF_{}([]"s"))
D1 == TRUE
ASSUME (x' /\ {Next, Nat})
THEOREM Init
====
