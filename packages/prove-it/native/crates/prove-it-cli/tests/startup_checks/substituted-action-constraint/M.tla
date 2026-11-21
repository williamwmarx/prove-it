---- MODULE M ----
EXTENDS Naturals
VARIABLES x, y
Next == x < 2 /\ x' = x + 1 /\ y' = y
Spec == x = 0 /\ y = 0 /\ [][Next]_<<x, y>>
CONSTANT Op(_)
T(a) == x < 1 \/ UNCHANGED y \/ y' = y
Inv == Op(TRUE)
====
