---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC, Randomization
CONSTANT C
RECURSIVE S(_)
G8(n) == S(n - 1) + 1
G7(n) == G8(n) + 0
G6(n) == G7(n) + 0
G5(n) == G6(n) + 0
G4(n) == G5(n) + 0
G3(n) == G4(n) + 0
G2(n) == G3(n) + 0
G1(n) == G2(n) + 0
S(n) == IF n = 0 THEN 0 ELSE G1(n)
D == S(150)
VARIABLE x
Init == x = 0
Next == x' = x
====
