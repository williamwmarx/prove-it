---- MODULE Spec ----
EXTENDS Naturals
CONSTANT c, S, F(_), G
VARIABLE x, r, f
Init == x = 0
Next == x' = x
D0 == ENABLED (((G + {}) + (F(x') => Nat)))
D1 == <>(IF F(x') THEN (<<>> ~> q) ELSE (F(x'))')
D2 == (F(1) ~> q)
ASSUME ENABLED ([q]_F(x'))
THEOREM F(1)
====
