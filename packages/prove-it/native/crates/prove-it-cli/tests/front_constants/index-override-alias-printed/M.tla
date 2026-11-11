---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
Foo == 1
Init == x = 0
Inv == x # 0
Al == [x |-> x, f |-> Foo]
Next == x' = x
Spec == Init /\ [][Next]_x
====
