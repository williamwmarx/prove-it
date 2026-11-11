---- MODULE Angle048 ----
EXTENDS Naturals, TLC
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
Inc == x' = (x + 1) % 3 /\ UNCHANGED y
Tog == y' = 1 - y /\ UNCHANGED x
Next == Inc \/ Tog
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
A == x' = (x + 1) % 3
P == [](x = 0 => <><<A>>_vars) /\ []<><<A>>_y
====
