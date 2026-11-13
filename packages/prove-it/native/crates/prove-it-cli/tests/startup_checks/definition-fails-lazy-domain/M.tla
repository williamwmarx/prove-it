---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, Bags, TLC
VARIABLE x
D == PrintT({DOMAIN [b \in SUBSET {1} |-> 1] \ (3 .. 3), CHOOSE y \in {} : TRUE})
ASSUME D
Init == x = 0
Next == x' = x
====
