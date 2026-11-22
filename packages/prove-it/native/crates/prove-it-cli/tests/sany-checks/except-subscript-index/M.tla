---- MODULE M ----
VARIABLE x
f == [i \in {1} |-> [h |-> i]]
A == x' = x
ASSUME [f EXCEPT ![[][A]_x].h = 1, ![1, [][A]_x] = [h |-> 2]] = f
====
