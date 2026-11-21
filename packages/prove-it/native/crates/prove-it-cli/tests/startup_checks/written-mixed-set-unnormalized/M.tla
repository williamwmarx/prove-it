---- MODULE M ----
EXTENDS Integers, FiniteSets, Bags, TLC
CONSTANT mv
VARIABLE x
Test == /\ PrintT(({1, 2} \ {2}) \cap {1, "a"})
        /\ PrintT({} \cap {1, "a"})
        /\ PrintT({1} \subseteq {1, "a"})
        /\ PrintT({1, "a"} \in 3..1)
        /\ PrintT(mv = {1, "a"})
        /\ PrintT(IsFiniteSet({1, "a"}))
        /\ PrintT(IsABag({1, "a"}))
ASSUME Test
Init == x = 0
Next == x' = x
Inv == ({x} \ {1}) \subseteq {0, "a"}
====
