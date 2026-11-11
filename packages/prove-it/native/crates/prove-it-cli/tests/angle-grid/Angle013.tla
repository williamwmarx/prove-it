---- MODULE Angle013 ----
EXTENDS Naturals, TLC
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
Inc == x' = (x + 1) % 3 /\ UNCHANGED y
Tog == y' = 1 - y /\ UNCHANGED x
Next == Inc \/ Tog
Spec == Init /\ [][Next]_vars
A == x' = (x + 1) % 3
P == <>[](y = 0) \/ []<><<A>>_<<x, y>>
====
