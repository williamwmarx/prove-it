---- MODULE AliasPrintLasso ----
EXTENDS Naturals, TLC
VARIABLES x, y
Init == x = 0 /\ y = 0
Next == (x < 2 /\ x' = x + 1 /\ y' = y /\ PrintT(<<"next", x>>)) \/ (x = 2 /\ UNCHANGED <<x, y>>)
Spec == Init /\ [][Next]_<<x, y>> /\ WF_<<x, y>>(x < 2 /\ x' = x + 1 /\ y' = y)
P == <>(x = 5)
Al == [x |-> x, p |-> PrintT(<<"alias", x>>)]
====
