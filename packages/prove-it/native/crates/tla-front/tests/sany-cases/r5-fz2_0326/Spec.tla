---- MODULE Spec ----
EXTENDS Naturals
CONSTANT c, S, F(_), G
VARIABLE x, r, f
Init == x = 0
Next == x' = x
D0 == ([CHOOSE q \in Next : Undef]_{} + \EE q : \E q \in F(1) : f[1])
ASSUME TRUE
THEOREM [x EXCEPT ![1] = F(x')]
====
