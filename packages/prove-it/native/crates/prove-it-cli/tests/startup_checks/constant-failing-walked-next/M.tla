---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, Bags, TLC
VARIABLE x
M == 1 = 1 /\ 1 = "a"
Init == x = 0
Next == M /\ x' = 1 - x
====
