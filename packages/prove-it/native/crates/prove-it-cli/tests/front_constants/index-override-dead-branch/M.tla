---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
Foo == 1
Init == x = 0 /\ IF FALSE THEN PrintT(Foo) ELSE TRUE
Next == x' = x
Spec == Init /\ [][Next]_x
====
