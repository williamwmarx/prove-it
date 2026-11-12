---- MODULE Spec ----
EXTENDS Naturals
CONSTANT c, S, F(_), G
VARIABLE x, r, f
Init == x = 0
Next == x' = x
D0 == q
D1 == F(1)
D2 == SF_[x EXCEPT ![1] = (r.a)'](<>(f[1]))
ASSUME (\E q \in f[1] : Init \cdot (S \/ TRUE))
====
