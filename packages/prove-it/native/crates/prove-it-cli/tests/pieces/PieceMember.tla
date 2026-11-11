---- MODULE PieceMember ----
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
Pick(p) == y' \in {0, 1, "a"} /\ y' # "a" /\ UNCHANGED x
Next == /\ \E p \in P : Inc(p) \/ Reset(p) \/ Pick(p)
Spec == Init /\ [][Next]_vars /\ WF_vars(\E p \in P : Pick(p) \/ Inc(p))
Live == []<>(y = 1)
====
