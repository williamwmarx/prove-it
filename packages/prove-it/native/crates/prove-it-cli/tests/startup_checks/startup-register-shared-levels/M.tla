---- MODULE M ----
EXTENDS Naturals, TLC
Drawn == RandomElement(1..1000000)
ASSUME TLCSet(1, Drawn)
ASSUME PrintT(<<"set", TLCGet(1) = Drawn>>)
VARIABLES n, d
Init == n = 0 /\ d = Drawn
Next == \/ n = 0 /\ n' \in 1..4000 /\ d' = d
        \/ n \in 1..4000 /\ n' = n + 4000 /\ d' = Drawn
====
