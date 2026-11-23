---- MODULE DotActions ----
EXTENDS Naturals
VARIABLES a, b
Init == a \in 0..3 /\ b = "q\"x"
A == a < 30 /\ a' = a + 1 /\ UNCHANGED b
B == a' = (a * 7) % 31 /\ b' = b
C == UNCHANGED <<a, b>>
Next == A \/ B \/ C
====
