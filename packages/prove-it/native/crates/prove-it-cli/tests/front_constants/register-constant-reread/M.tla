---- MODULE M ----
EXTENDS Naturals, TLC, TLCExt, Sequences, FiniteSets
VARIABLE x
C == TLCEval(TLCGetAndSet(3, LAMBDA a, b: a + b, 1, 0))
Inv == C = C
Init == x = 0
Next == x' = (x + 1) % 2
Spec == Init /\ [][Next]_x

====
