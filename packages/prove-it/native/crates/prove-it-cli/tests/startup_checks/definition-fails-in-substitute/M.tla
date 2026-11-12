---- MODULE M ----
EXTENDS Naturals, TLC, Sequences, FiniteSets
VARIABLE x
I == INSTANCE N WITH c <- IF Assert(FALSE, "sub") THEN 1 ELSE 2
Init == x = I!Val
Next == x' = x
Spec == Init /\ [][Next]_x
====
