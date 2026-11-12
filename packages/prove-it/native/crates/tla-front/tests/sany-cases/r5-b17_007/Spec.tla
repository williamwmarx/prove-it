---- MODULE Spec ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = x
A == [x EXCEPT ![1] = SF_@(Next)]
====
