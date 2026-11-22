---- MODULE M ----
VARIABLE x
f == [v \in {1} |-> v]
A == [f EXCEPT !.a.b[[]x, 2] = (1)]
B == [f EXCEPT ![1].a[[]x, 2] = 1]
C == [f EXCEPT ![[]x, 1][<>x, 2] = 1]
D == [f EXCEPT ![1][x, 2] = 1]
Init == x = 0
Next == x' = x
====
