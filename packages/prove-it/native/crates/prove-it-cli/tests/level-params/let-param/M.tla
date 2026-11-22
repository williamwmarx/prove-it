---- MODULE M ----
VARIABLE x
Init == x = 0
Next == x' = x
P == LET A(p) == p' = p IN x \in {0, 1}
====
