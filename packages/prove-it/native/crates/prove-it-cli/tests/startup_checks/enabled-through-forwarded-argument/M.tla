---- MODULE M ----
EXTENDS Naturals, Sequences, FiniteSets, TLC
VARIABLE x
Next == x < 2 /\ x' = x + 1
Spec == x = 0 /\ [][Next]_x /\ WF_x(Next)
Over(F(_)) == ENABLED F(2)
Outer(G(_)) == Over(G)
Prop == [](Outer(LAMBDA n : x = n /\ x' = n))
====
