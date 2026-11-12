---- MODULE M ----
EXTENDS Naturals, TLC, TLCExt, Sequences, FiniteSets
VARIABLE x
MyPrint(a) == PrintT(a)
MyEq(a, b) == AssertEq(a, b)
C == 0
D == PrintT("d")
Init == x = 0
Next == x' = (x + 1) % 3
Spec == Init /\ [][Next]_x
ASSUME IF 1 = 2 THEN C = C ELSE TRUE

====
