---- MODULE M ----
EXTENDS Naturals
CONSTANT F(_)
Apply(Op(_), a) == Op(a)
VARIABLE x
Init == x = Apply(F, 1)
Next == x' = x
Inv == x = 5
====
