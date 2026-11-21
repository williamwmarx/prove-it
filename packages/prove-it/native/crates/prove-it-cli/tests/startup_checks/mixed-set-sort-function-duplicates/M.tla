---- MODULE M ----
EXTENDS Integers, TLC, Sequences
VARIABLE x
ASSUME PrintT({<<"a">>, [i \in {1} |-> "a"]})
Init == x = 0
Next == x' = x
====
