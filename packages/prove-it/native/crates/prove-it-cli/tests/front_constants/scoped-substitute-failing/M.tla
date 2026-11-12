---- MODULE M ----
EXTENDS Naturals, TLC, Sequences, FiniteSets
VARIABLE x
I == INSTANCE Inner
E == 1 \div 0 = 1
Inv == I!IInv
Init == x = 0
Next == x' = (x + 1) % 3
Spec == Init /\ [][Next]_x

====
