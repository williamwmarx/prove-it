---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x \in {1, 0}
Next == x' = (x + 1) % 4
V == 1 \div x
====
