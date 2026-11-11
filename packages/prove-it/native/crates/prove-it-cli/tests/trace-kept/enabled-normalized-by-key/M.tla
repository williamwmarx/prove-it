---- MODULE M ----
EXTENDS Naturals
VARIABLE x, y
Init == x = 0 /\ y = {}
F(v) == (v = TRUE) /\ ENABLED (x' = 1 /\ y' = {3,1,2} /\ (v = TRUE) /\ "a" \in y')
Next == x' = 1 /\ y' = {} /\ F(x = 0)
====
