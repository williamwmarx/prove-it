---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
Foo == 1
Bar == PrintT(Foo)
Init == x = 0
Next == x' = x
Spec == Init /\ [][Next]_x
====
