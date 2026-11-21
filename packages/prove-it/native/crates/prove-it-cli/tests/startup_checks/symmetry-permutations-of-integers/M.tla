---- MODULE M ----
EXTENDS Naturals, TLC
CONSTANT A, B
VARIABLE x
Init == x \in {A, B}
Next == x' = x
Sym == Permutations({A, B}) \cup {(A :> 1) @@ (B :> B)}
====
