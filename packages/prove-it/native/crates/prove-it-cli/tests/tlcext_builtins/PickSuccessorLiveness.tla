---- MODULE PickSuccessorLiveness ----
EXTENDS Naturals, TLCExt
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
Spec == Init /\ [][Next]_x /\ WF_x(Next)
Prop == []<>(x = 1 /\ PickSuccessor(TRUE))
====
