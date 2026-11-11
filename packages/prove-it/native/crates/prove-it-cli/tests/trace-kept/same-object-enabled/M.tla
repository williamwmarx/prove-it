---- MODULE M ----
EXTENDS Naturals
VARIABLE x, y
Init == x = 0 /\ y = {}
F(v) == (v = TRUE) /\ (v = TRUE) /\ "a" \in y'
Next == x' = x + 1 /\ y' = y
Inv == ENABLED (y' = {3, 1, 2} /\ x' = 1 /\ F(x = 0))
====
