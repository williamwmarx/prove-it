---- MODULE M ----
EXTENDS Integers, Sequences, TLC
Test == PrintT(Append(BOOLEAN, Nat))
VARIABLE x
Init == x = TRUE
Next == UNCHANGED x
Inv == x /\ Test
====
