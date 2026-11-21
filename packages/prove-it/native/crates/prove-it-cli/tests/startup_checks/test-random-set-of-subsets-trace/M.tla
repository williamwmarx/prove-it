---- MODULE M ----
EXTENDS Randomization, FiniteSets, Naturals, TLC
VARIABLE x, y
Init == x = 0 /\ y = TestRandomSetOfSubsets(4, 2, 1..5)
Next == x < 2 /\ x' = x + 1 /\ y' = TestRandomSetOfSubsets(4, 2, 1..(x + 4))
====
