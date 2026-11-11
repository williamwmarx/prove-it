---- MODULE M ----
EXTENDS Naturals, TLC
CONSTANT S
VARIABLE x
Ignore(a) == TRUE
Once(a) == a = 1
Ignore2(a) == Ignore(a) /\ Ignore(a)
C == \A v \in {1} : Ignore(v \div 0)
Init == x = 0
Next == x' = x
Spec == C /\ Init /\ [][Next]_x
====
