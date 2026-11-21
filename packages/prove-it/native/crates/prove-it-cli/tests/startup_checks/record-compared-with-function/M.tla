---- MODULE M ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x < 2 /\ x' = x + 1
Inv == x = 0 \/ [a |-> 1] = <<x>>
====
