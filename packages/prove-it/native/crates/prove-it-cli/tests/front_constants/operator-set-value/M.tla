---- MODULE M ----
EXTENDS Naturals
CONSTANT F(_, _)
VARIABLE x
Init == x \in F(1, 2)
Next == x' = x
Inv == x /= "b"
====
