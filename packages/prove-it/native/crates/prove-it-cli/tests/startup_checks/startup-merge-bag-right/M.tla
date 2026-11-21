---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, Bags, TLC
Test == PrintT(Nat @@ SetToBag({1,2}))
ASSUME Test
====
