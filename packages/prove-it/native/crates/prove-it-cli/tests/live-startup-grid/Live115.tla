---- MODULE Live115 ----
EXTENDS Naturals, TLC
VARIABLE x
Z == PrintT("z")
Init == x = 0
Next == x' = x
Spec == Init /\ [][Next]_x
P == <>(x = 1) \/ [](3)
====
