---- MODULE M ----
EXTENDS Integers, Sequences, TLC
Test == PrintT(Append(Nat, {1,"a"}))
VARIABLE x
Init == x = TRUE
Next == x' = Test
====
