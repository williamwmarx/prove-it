---- MODULE P ----
EXTENDS Naturals
VARIABLE x
K == 1
J == 1
Init == x = J + K
Next == x' = x
Inv == x = 2
====
