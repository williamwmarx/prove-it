---- MODULE M ----
EXTENDS Naturals
VARIABLE x
Init == x \in 1..3 /\ 1 \div (x - 2) = 0
Next == x' = x
====
