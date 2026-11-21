---- MODULE M ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x < 2 /\ x' = IF x = 1 /\ [a |-> 1] = <<x>> THEN 5 ELSE x + 1
====
