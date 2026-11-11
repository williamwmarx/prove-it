---- MODULE M ----
EXTENDS Naturals
VARIABLE x, y
Init == x = 0 /\ y = {}
Next == y' = {3, 1, 2} /\ x' = 1 /\ TRUE = (LET v == (x = 0) IN v /\ v /\ "a" \in y')
====
