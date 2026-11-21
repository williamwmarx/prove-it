---- MODULE PruneRegisterGuard ----
EXTENDS Naturals, TLC
CONSTANT S
VARIABLE x
Seen == TLCGet(1)
Init == x = <<0, 0>> /\ TLCSet(1, 0)
Next ==
    /\ x' \in [1..2 -> 0..2]
    /\ x'[1] >= Seen
    /\ \A j \in {2} : x'[j] = x[j]
    /\ TLCSet(1, x'[1] + 1)
Inv == TRUE
====
