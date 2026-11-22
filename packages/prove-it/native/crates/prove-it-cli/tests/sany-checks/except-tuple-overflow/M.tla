---- MODULE M ----
VARIABLE x
f == [v \in {1} |-> v]
A == [f EXCEPT ![1][2][3][[]x, 4] = 1]
Init == x = 0
Next == x' = x
====
