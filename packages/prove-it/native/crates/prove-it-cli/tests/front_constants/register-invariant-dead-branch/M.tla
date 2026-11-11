---- MODULE M ----
EXTENDS Naturals, TLC, TLCExt, Sequences, FiniteSets
VARIABLE x

Inv == IF FALSE THEN TLCGetOrDefault(1, TRUE) ELSE TRUE
Init == x = 0
Next == x' = (x + 1) % 2
Spec == Init /\ [][Next]_x

====
