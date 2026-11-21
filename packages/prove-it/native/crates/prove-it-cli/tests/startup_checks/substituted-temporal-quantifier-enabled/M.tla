---- MODULE M ----
EXTENDS Naturals
VARIABLE x
Next == x < 2 /\ x' = x + 1
Spec == x = 0 /\ [][Next]_x
CONSTANT Op(_)
T(a) == \AA y : y = 0
Prop == []ENABLED Op(TRUE)
====
