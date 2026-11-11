---- MODULE Spec ----
EXTENDS Naturals
CONSTANT c, S, F(_), G
VARIABLE x, r, f
Init == x = 0
Next == x' = x
D0 == lab:: [WF_x(CHOOSE q \in 1 : f[1])]_{1, F(x')}
D1 == <>(UNCHANGED @)
D2 == c
====
