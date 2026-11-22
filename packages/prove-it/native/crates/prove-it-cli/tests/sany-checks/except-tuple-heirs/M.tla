---- MODULE M ----
VARIABLE x
f == [v \in {1} |-> v]
A == [f EXCEPT ![[]x, 1] = 1]
B == [f EXCEPT ![1][[]x, 2] = 1]
C == [f EXCEPT ![1][2][[]x, 3] = ((1))]
D == [f EXCEPT !.a[[]x, 2] = 1]
E == [f EXCEPT ![1][[]x, 2][3] = 1]
G == [f EXCEPT ![[]x, 1][2] = 1, !["a"][<>x, 2] = 1 = 2]
H == [f EXCEPT ![1][2][[]x, 3] = [f EXCEPT ![1][<>x, 2] = 3]]
Init == x = 0
Next == x' = x
====
