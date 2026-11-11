---- MODULE Angle006 ----
EXTENDS Naturals, TLC
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
Inc == x' = (x + 1) % 3 /\ UNCHANGED y
Tog == y' = 1 - y /\ UNCHANGED x
Next == Inc \/ Tog \/ UNCHANGED vars
Spec == Init /\ [][Next]_vars /\ WF_x(Inc)
A == PrintT(<<"A", x, x'>>) /\ (x' - x) \div (x' - x) # 0
P == []<><<A>>_<<x, y>>
====
