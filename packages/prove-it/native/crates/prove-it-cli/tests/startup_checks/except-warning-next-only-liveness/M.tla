---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
Init == x = 0
Next == x' = [<<1 - x>> EXCEPT ![2] = 1][1]
Spec == Init /\ [][Next]_x
P == []<>(x = 1)
====
