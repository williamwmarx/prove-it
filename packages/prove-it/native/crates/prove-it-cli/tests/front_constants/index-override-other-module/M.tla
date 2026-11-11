---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
Foo == 1
Init == x = Foo /\ PrintT(Foo)
Next == x' = x
Spec == Init /\ [][Next]_x
====
