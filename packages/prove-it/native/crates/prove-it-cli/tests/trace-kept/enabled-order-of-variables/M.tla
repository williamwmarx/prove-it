---- MODULE M ----
EXTENDS Naturals
VARIABLE y, x
Init == x = 0 /\ y = {}
F(v) == (v = TRUE) /\ ENABLED (y' = {3,1,2} /\ (v = TRUE) /\ "a" \in y')
Next == x' = 1 /\ y' = {} /\ F(x = 0)
====
