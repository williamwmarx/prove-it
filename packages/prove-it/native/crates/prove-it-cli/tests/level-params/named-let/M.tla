---- MODULE M ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 2
Q == LET A == x' = x IN x \in {0, 1}
P == Q
====
