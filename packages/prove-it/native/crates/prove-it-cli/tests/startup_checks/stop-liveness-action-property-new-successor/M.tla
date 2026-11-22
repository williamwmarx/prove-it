---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
Next == x < 2 /\ x' = x + 1
Spec == x = 0 /\ [][Next]_x
P1 == [][x' < 1]_x
P2 == [](x = 1 => [](x = 1))
====
