---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
IncX == x < 3 /\ x' = x + 1 /\ UNCHANGED y
IncY == y < 2 /\ y' = y + 1 /\ UNCHANGED x
Reset == x = 3 /\ x' = 0 /\ y' = 0
Next == IncX \/ IncY \/ Reset
Spec == Init /\ [][Next]_vars
FairSpec == Spec /\ WF_vars(Next)
AC == {x'}
P == []<>(x = 0)
====
