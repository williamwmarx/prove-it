---- MODULE M ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = x
Spec == Init /\ [][Next]_x
P == \E k \in [Nat -> {1}] : <>(x = k)
====
