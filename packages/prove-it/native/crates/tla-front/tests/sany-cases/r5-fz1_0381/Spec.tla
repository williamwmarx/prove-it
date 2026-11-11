---- MODULE Spec ----
EXTENDS Naturals
CONSTANT c, S, F(_), G
VARIABLE x, r, f
Init == x = 0
Next == x' = x
D0 == UNCHANGED Next
D1 == [x EXCEPT ![1] = [q]_{}]
D2 == [x EXCEPT ![1] = f[1]]
====
