---- MODULE PostconditionConstant ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
Holds == x \in Nat
Never == FALSE
====
