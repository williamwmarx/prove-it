---- MODULE Angle070 ----
EXTENDS Naturals, TLC
VARIABLES x
Init == x = 0
Next == x' = (x + 1) % 3
Spec == Init /\ [][Next]_x /\ WF_x(Next)
Prop == <>[][x = 9]_(Print(x, x))
====
