---- MODULE M ----
EXTENDS Naturals, TLC
CONSTANT a, b
VARIABLE x
Init == x = 0
Next == x < 2 /\ x' = x + 1
B == Print("b", TRUE)
Sym == Permutations({a, b})
====
