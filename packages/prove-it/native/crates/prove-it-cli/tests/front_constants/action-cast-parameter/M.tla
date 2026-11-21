---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x = 0
B(p) == x' = (x + 1) % 3 \/ p
Next == B(FALSE)
====
