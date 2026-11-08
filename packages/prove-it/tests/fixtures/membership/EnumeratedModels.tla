---- MODULE EnumeratedModels ----
EXTENDS Naturals
CONSTANTS M, T
VARIABLE x
Inv == TRUE \notin {M} \cup {T}
Init == x = 0
Next == x < 2 /\ x' = x + 1
Spec == Init /\ [][Next]_x
====
