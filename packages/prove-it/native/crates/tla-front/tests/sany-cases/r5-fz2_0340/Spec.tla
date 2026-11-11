---- MODULE Spec ----
EXTENDS Naturals
CONSTANT c, S, F(_), G
VARIABLE x, r, f
Init == x = 0
Next == x' = x
D0 == (Init => (f[1] /\ SF_[x EXCEPT ![1] = <<>>](x')))
D1 == ((f[1] + <<>>) \/ \E q \in 1 : x')
D2 == (r.a + WF_x("s"))
====
