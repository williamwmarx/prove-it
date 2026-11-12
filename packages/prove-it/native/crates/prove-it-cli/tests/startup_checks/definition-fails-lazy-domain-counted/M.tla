---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, Bags, TLC
VARIABLE x
D == PrintT((Cardinality(DOMAIN [b \in SUBSET {1} |-> b]) :> Head(<<>>)))
ASSUME D
Init == x = 0
Next == x' = x
====
