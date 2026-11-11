---- MODULE PickSuccessorProperty ----
EXTENDS Naturals, TLCExt
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
Spec == Init /\ [][Next]_x
Prop == []PickSuccessor(TRUE)
====
