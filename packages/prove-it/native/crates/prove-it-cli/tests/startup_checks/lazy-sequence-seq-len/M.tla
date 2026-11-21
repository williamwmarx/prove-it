---- MODULE M ----
EXTENDS Integers, Sequences, TLC
VARIABLE x
Spec == x = TRUE /\ [][UNCHANGED x]_x
Prop == [](PrintT(Len([i \in Seq({1}) |-> i])))
====
