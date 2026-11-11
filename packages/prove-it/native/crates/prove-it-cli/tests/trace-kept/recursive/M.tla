---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x = 0
RECURSIVE R(_, _)
R(n, F) == IF n = 0 THEN F[0] = x' ELSE R(n - 1, F)
Next == x' \in {1, 2} /\ R(3, [i \in Nat |-> x'])
Inv == x # 2
====
