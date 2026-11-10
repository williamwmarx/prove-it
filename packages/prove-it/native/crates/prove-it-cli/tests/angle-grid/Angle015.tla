---- MODULE Angle015 ----
EXTENDS Naturals, TLC
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
Inc == x' = (x + 1) % 3 /\ UNCHANGED y
Tog == y' = 1 - y /\ UNCHANGED x
Next == (x < 2 /\ Inc) \/ Tog
Spec == Init /\ [][Next]_vars /\ SF_vars(Inc) /\ WF_y(Tog)
A == PrintT(<<"A", x, y, x', y'>>) /\ x' # x
P == <>[](y = 0) \/ []<><<A>>_<<x, y>>
====
