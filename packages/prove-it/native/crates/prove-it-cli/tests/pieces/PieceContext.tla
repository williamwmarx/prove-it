---- MODULE PieceContext ----
EXTENDS Naturals
CONSTANT P
VARIABLES x, y
vars == <<x, y>>
Init == x = [p \in P |-> 0] /\ y = 0
Inc(p) == x[p] < 2 /\ x' = [x EXCEPT ![p] = x[p] + 1] /\ UNCHANGED y
Reset(p) == x[p] = 2 /\ x' = [x EXCEPT ![p] = 0] /\ UNCHANGED y
Twice(p) == x[p] = 0 /\ x' = [x EXCEPT ![p] = 1] /\ UNCHANGED y
Flip == y' = 1 - y /\ UNCHANGED x
Stay == UNCHANGED vars
Next == (y = 0 /\ Inc(1)) \/ Reset(1) \/ Flip
Spec == Init /\ [][Next]_vars /\ WF_vars(Inc(1))
Live == []<>(x[1] = 2)
====
