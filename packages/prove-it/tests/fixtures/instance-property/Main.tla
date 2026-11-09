---- MODULE Main ----
EXTENDS Naturals
VARIABLE x
A == INSTANCE Abs
Init == x = 0
Next == x' = x + 1
Spec == Init /\ [][Next]_x
PSafe == A!Safe
PSafe2 == A!Safe2
====
