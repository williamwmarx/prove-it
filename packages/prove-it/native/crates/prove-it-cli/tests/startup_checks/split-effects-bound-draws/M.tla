---- MODULE M ----
EXTENDS Naturals, TLC, Randomization
VARIABLE y
Init == y \in 0..3
Next == \E v \in RandomSubset(1, 10..19) : y' = v % 4 /\ PrintT(<<y, v>>)
====
