---- MODULE M ----
EXTENDS Integers, Sequences, TLC
VARIABLE x
Spec == x = TRUE /\ [][UNCHANGED x]_x
Prop == [](PrintT("a" \o ([{1,2}->{1,2}])))
====
