---- MODULE M ----
EXTENDS Integers, Sequences, TLC
VARIABLE x
Spec == x = TRUE /\ [][UNCHANGED x]_x
Prop == [](PrintT(<<>> \o ([i \in Nat |-> i])))
====
