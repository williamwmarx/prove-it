---- MODULE M ----
EXTENDS Integers, Sequences, TLC
Test == PrintT(Append(BOOLEAN, Nat))
VARIABLE x
Init == x = Test
Next == UNCHANGED x
====
