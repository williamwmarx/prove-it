---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
VARIABLE x
Init == x = IsFiniteSet([a : Int, b : {1}] \cap [a : Nat, b : {1}])
Next == x' = x
====
