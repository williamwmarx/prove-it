---- MODULE M ----
EXTENDS Naturals, TLC, Sequences
VARIABLE x
Foo == 1
Init == x = 0 /\ PrintT(Len(<<1,2>>))
Next == x' = x
Spec == Init /\ [][Next]_x
====
