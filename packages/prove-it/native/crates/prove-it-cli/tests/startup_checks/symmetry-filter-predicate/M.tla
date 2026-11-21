---- MODULE M ----
EXTENDS Naturals, TLC
CONSTANT S, T
VARIABLE x
Init == x \in S
Next == x' = x
Sym == {f \in Permutations(T) : TRUE}
====
