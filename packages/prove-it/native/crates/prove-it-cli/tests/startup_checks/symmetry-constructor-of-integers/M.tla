---- MODULE M ----
EXTENDS Naturals, TLC
CONSTANT A, B
VARIABLE x
Init == x \in {A, B}
Next == x' = x
Sym == {[i \in 1..2 |-> A], [i \in 1..2 |-> B]} \cup {A :> B}
====
