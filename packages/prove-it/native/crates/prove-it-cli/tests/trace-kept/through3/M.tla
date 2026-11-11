---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x = 0
Q(A, B) == /\ x' \in {1, 2} /\ A[0] = x' /\ B[0] = x'
R(C) == Q(C, C)
P(F) == R(F)
Next == P([i \in Nat |-> x'])
Inv == x # 2
====
