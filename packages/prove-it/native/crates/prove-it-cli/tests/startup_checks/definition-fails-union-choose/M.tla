---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, Bags, TLC
VARIABLE x
D == PrintT(CHOOSE b \in UNION {{}, {}} : TRUE)
ASSUME D
Init == x = 0
Next == x' = x
====
