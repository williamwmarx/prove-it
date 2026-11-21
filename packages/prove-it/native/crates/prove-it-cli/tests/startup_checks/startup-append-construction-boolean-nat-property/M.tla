---- MODULE M ----
EXTENDS Integers, Sequences, TLC
Test == PrintT(Append(BOOLEAN, Nat))
VARIABLE x
Spec == x = TRUE /\ [][UNCHANGED x]_x
Prop == [](x /\ Test)
====
