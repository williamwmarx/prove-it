---- MODULE M ----
EXTENDS Naturals
VARIABLE x
Init == x \in 0..2
Next == x' = (x + 1) % 3
====
