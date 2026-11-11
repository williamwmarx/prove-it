---- MODULE M ----
EXTENDS Naturals, TLC, TLCExt, Sequences, FiniteSets
VARIABLE x
Inv == TLCGetOrDefault(3, 0) = TLCGetOrDefault(3, 0)
Init == x = 0
Next == x' = (x + 1) % 2
Spec == Init /\ [][Next]_x

====
