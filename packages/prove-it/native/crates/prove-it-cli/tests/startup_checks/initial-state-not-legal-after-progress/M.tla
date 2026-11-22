---- MODULE M ----
EXTENDS Naturals
VARIABLE x
Init == \E i \in 1..5 : i < 5 => x = i
Next == x' = x
====
