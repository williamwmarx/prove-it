---- MODULE M ----
EXTENDS Naturals, TLC
CONSTANT S, T
VARIABLE x
Init == x \in S
Next == x' = x
P == Permutations(T)
Sym == P
====
