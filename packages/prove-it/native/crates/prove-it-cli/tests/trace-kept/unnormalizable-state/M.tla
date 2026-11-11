---- MODULE M ----
EXTENDS Naturals
VARIABLE x, y
Init == x = 0 /\ y = {}
F(T, v) == \E i \in {1, 2} : /\ y' = (IF i = 1 THEN T ELSE {1, "a"})
                             /\ v = TRUE
                             /\ i = 2
                             /\ "a" \in T
Next == x' = 1 /\ F({3, 1, 2}, x = 0)
====
