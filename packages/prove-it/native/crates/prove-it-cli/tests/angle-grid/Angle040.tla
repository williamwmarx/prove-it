---- MODULE Angle040 ----
EXTENDS Naturals, TLC
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
Inc == x' = (x + 1) % 3 /\ UNCHANGED y
Tog == y' = 1 - y /\ UNCHANGED x
Next == Inc \/ Tog
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
A == PrintT(<<"A", x, y, x', y'>>) /\ x' # x
P == \E i \in {0} : <>[](y = i) \/ []<><<A>>_<<y, x>>
====
