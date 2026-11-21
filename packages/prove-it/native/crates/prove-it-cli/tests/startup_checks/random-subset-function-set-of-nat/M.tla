---- MODULE M ----
EXTENDS Randomization, FiniteSets, Naturals
ASSUME RandomSubset(1, [{1, 2} -> Nat]) = {}
====
