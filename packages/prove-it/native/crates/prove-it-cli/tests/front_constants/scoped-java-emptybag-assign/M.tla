---- MODULE M ----
EXTENDS Bags
VARIABLE x
Init == x = 0
Next == x' = x
Inv == EmptyBag = [a |-> 1]
====
