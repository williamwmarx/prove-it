---- MODULE PruneRegister ----
EXTENDS Naturals, TLC
CONSTANT S
VARIABLE x
Init == x = <<0, 0>> /\ TLCSet(1, 0)
Next ==
    /\ x' \in [1..2 -> 0..1]
    /\ \A j \in {2} : x'[j] = TLCGet(1)
    /\ TLCSet(1, 1)
Inv == x[2] = 0
====
